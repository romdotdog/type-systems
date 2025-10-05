module algorithm-w

import hm-expr
import std/data/linearset
import std/data/linearmap
import std/test

type ty
  TUnit
  TFn(tau1 : ty, tau2 : ty)
  TVar(id : int)

fun ty/show(this : ty, left = False) : <div,read<global>> string
  match this
    TUnit -> "()"
    TFn(tau1, tau2) -> 
      if left then
        "(" ++ tau1.show(True) ++ " -> " ++ tau2.show ++ ")"
      else
        tau1.show(True) ++ " -> " ++ tau2.show
    TVar(id) -> char(97 + id).string

fun ty/(==)(t1 : ty, t2 : ty)
  match (t1, t2)
    (TUnit, TUnit) -> True
    (TVar(id1), TVar(id2)) -> id1 == id2
    (TFn(p1, r1), TFn(p2, r2)) -> p1 == p2 && r1 == r2
    _ -> False

type ty-scheme
  Mono(t : ty)
  Poly(vars : linearSet<int>, t : ty)

effect fresh
  fun new-var() : int

struct env(vars : list<(int, ty-scheme)>)

fun lookup(env : env, id : int)
  env.vars.lookup fn(id') id == id'

fun extend(env : env, id : int, scheme : ty-scheme)
  Env(Cons((id, scheme), env.vars))

effect val gamma : env

alias subst = linearMap<int, ty>

// composition
fun after(post : subst, pre : subst)
  pre.union(post.map(fn(k, v) v.do-sub(pre)))

fun ty/free-vars(t : ty) : <div,read<global>> linearSet<int>
  match t
    TUnit -> linear-set([])
    TVar(id) -> linear-set([id])
    TFn(param, result) -> 
      free-vars(param) + free-vars(result)

fun ty-scheme/free-vars(sigma : ty-scheme) : <div,read<global>> linearSet<int>
  match sigma
    Mono(tau) -> tau.free-vars()
    Poly(vars, tau) -> tau.free-vars() - vars

fun env/free-vars(env : env) : <div,read<global>> linearSet<int>
  env.vars.map(fn((_, scheme)) scheme.free-vars()).foldr(linear-set([]), set/(+))

fun new-tvar()
  TVar(new-var())

fun infer(expr : expr) : <st<global>,div,exn,fresh,gamma> (ty, subst)
  match expr
    Unit -> (TUnit, LinearMap([]))
    Var(x) -> 
      match gamma.lookup(x)
        Just(sigma) -> (sigma.instantiate(), LinearMap([]))
        Nothing -> throw("unbound variable")
    App(e0, e1) ->
      val (tau0, s0) = e0.infer()
      val (tau1, s1) = (handler { val gamma = gamma.do-sub(s0) }) fn() e1.infer()
      val tau' = new-tvar()
      val s2 = mgu(tau0.do-sub(s1), TFn(tau1, tau'))
      (tau'.do-sub(s2), s2.after(s1).after(s0))
    Abs(x, e) ->
      val tau = new-tvar()
      with val gamma = gamma.extend(x, Mono(tau))
      val (tau', s) = e.infer()
      (TFn(tau.do-sub(s), tau'), s)
    Let(x, e0, e1) ->
      val (tau, s0) = e0.infer()
      with val gamma = gamma.do-sub(s0).extend(x, tau.generalize())
      val (tau', s1) = e1.infer()
      (tau', s1.after(s0))

fun mgu(t1 : ty, t2 : ty)
  match (t1, t2)
    (TUnit, TUnit) -> LinearMap([])
    (TVar(a-id), b) -> 
      if t1 == t2 then LinearMap([]) else
        if a-id.occurs-in(b) then throw("occurs check") else
          LinearMap([(a-id, b)])
    (a, TVar(b-id)) ->
      if t1 == t2 then LinearMap([]) else
        if b-id.occurs-in(a) then throw("occurs check") else
          LinearMap([(b-id, a)])
    (TFn(a, b), TFn(c, d)) ->
      val s1 = mgu(a, c)
      val s2 = mgu(b.do-sub(s1), d.do-sub(s1))
      s1.after(s2)
    _ -> throw("type error")

fun occurs-in(id : int, t : ty)
  match t
    TUnit -> False
    TVar(id') -> id == id'
    TFn(t1, t2) -> id.occurs-in(t1) || id.occurs-in(t2)

fun generalize(t : ty) : <div,gamma,read<global>> ty-scheme
  val to-quantify = t.free-vars() - gamma.free-vars()
  if to-quantify.is-empty then 
    Mono(t)
  else 
    Poly(to-quantify, t)

effect subst-eff
  fun lookup-var(id : int) : maybe<ty>

fun instantiate(scheme : ty-scheme)
  match scheme
    Mono(t) -> t
    Poly(vars, t) -> 
      val new-tvars = vars.list().map(fn (id) (id, new-tvar()))
      with fun lookup-var(id) -> 
        new-tvars.lookup(id)
      t.substitute()

fun env/do-sub(env : env, subst : subst) : <div> env
  Env(env.vars.map(fn((k, scheme)) (k, scheme.do-sub(subst))))

fun ty-scheme/do-sub(scheme : ty-scheme, subst : subst) : <div> ty-scheme
  match scheme
    Mono(t) -> Mono(t.do-sub(subst))
    Poly(vars, t) -> 
      with fun lookup-var(id) -> 
        if vars.member(id) then // shouldn't apply substitutions to quantified vars
          Nothing
        else
          subst.lookup(id)
      Poly(vars, t.substitute())

fun ty/do-sub(t : ty, subst : subst) : <div> ty
  with fun lookup-var(id) -> subst.lookup(id)
  t.substitute()

fun substitute(t : ty)
  match t
    TUnit -> TUnit
    TVar(id) -> 
      match lookup-var(id)
        Just(new-t) -> new-t.substitute()
        Nothing -> t
    TFn(param, result) -> 
      TFn(param.substitute(), result.substitute())

fun run(expr : expr)
  var counter := 0
  with fun new-var() { counter := counter + 1; counter }
  with val gamma = Env([])
  val (tau, s) = expr.infer()
  tau.do-sub(s).show().println()

pub fun main()
  // id: \f.\x. f x  :  (a -> b) -> a -> b
  Abs(0, Abs(1, App(Var(0), Var(1)))).run()

  // twice: \f.\x. f (f x) : (a -> a) -> a -> a  
  Abs(0, Abs(1, App(Var(0), App(Var(0), Var(1))))).run()

  // (+): \m.\n.\f.\x. m f (n f x): (a -> b -> c) -> (a -> d -> b) -> a -> d -> c
  Abs(0, Abs(1, Abs(2, Abs(3, App(App(Var(0), Var(2)), App(App(Var(1), Var(2)), Var(3))))))).run()

  // succ: \n.\f.\x. f (n f x): ((a -> b) -> c -> a) -> (a -> b) -> c -> b
  Abs(0, Abs(1, Abs(2, App(Var(1), App(App(Var(0), Var(1)), Var(2)))))).run()

  // mult: \m.\n.\f.\x. m (n f) x: (a -> b -> c) -> (d -> a) -> d -> b -> c
  Abs(0, Abs(1, Abs(2, Abs(3, App(App(Var(0), App(Var(1), Var(2))), Var(3)))))).run()

  // pred: \n.\f.\x. n (\g.\h. h (g f)) (\u.x) (\u.u): (((a -> b) -> (b -> c) -> c) -> (d -> e) -> (f -> f) -> g) -> a -> e -> g
  Abs(0, Abs(1, Abs(2, App(App(App(Var(0), Abs(3, Abs(4, App(Var(4), App(Var(3), Var(1)))))), Abs(5, Var(2))), Abs(6, Var(6)))))).run()

  // let-identity: \x. let y = x in y: 'a -> 'a
  Abs(0, Let(1, Var(0), Var(1))).run()

  // let-identity-2: \f. \x. \y. let id = \z. z in f x (id x) y (id y)
  Abs(0, Abs(1, Abs(2, Let(3, Abs(4, Var(4)), App(App(App(App(Var(0), Var(1)), App(Var(3), Var(1))), Var(2)), App(Var(3), Var(2))))))).run()

  // let-const: \x. let y = \z.x in y: 'a -> 'b -> 'a
  Abs(0, Let(1, Abs(2, Var(0)), Var(1))).run()

