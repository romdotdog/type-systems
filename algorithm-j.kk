module algorithm-j

import hm-expr
import std/data/linearset
import std/test

type tyvar
  Bound(ty : ty)
  Unbound(id : int)

fun tyvar/show(this : tyvar, left : bool = False) : <div,read<global>> string
  match this
    Bound(ty) -> ty.show(left)
    Unbound(id) -> char(97 + id).string

fun tyvar/(==)(t1 : tyvar, t2 : tyvar)
  match (t1, t2)
    (Bound(t1), Bound(t2)) -> t1 == t2
    (Unbound(id1), Unbound(id2)) -> id1 == id2
    _ -> False

type ty
  TUnit
  TFn(tau1 : ty, tau2 : ty)
  TVar(cell : ref<global, tyvar>)

fun ty/show(this : ty, left = False) : <div,read<global>> string
  match this
    TUnit -> "()"
    TFn(tau1, tau2) -> 
      if left then
        "(" ++ tau1.show(True) ++ " -> " ++ tau2.show ++ ")"
      else
        tau1.show(True) ++ " -> " ++ tau2.show
    TVar(cell) -> (!cell).show(left)

fun ty/(==)(t1 : ty, t2 : ty)
  match (t1, t2)
    (TUnit, TUnit) -> True
    (TVar(cell1), TVar(cell2)) -> !cell1 == !cell2
    (TFn(p1, r1), TFn(p2, r2)) -> p1 == p2 && r1 == r2
    _ -> False

type ty-scheme
  Mono(t : ty)
  Poly(vars : linearSet<int>, t : ty)

effect fresh
  fun new-var() : int

struct env(vars: list<(int, ty-scheme)>)

fun lookup(env : env, id : int)
  env.vars.lookup fn(id') id == id'

fun extend(env : env, id : int, scheme : ty-scheme)
  Env(Cons((id, scheme), env.vars))

effect val gamma : env

fun ty/free-vars(t : ty) : <div,read<global>> linearSet<int>
  match t
    TUnit -> linear-set([])
    TVar(cell) ->
      match !cell
        Bound(t') -> free-vars(t')
        Unbound(id) -> linear-set([id])
    TFn(param, result) -> 
      free-vars(param) + free-vars(result)

fun ty-scheme/free-vars(sigma : ty-scheme) : <div,read<global>> linearSet<int>
  match sigma
    Mono(tau) -> tau.free-vars()
    Poly(vars, tau) -> tau.free-vars() - vars

fun env/free-vars(env : env) : <div,read<global>> linearSet<int>
   env.vars.map(fn((_, scheme)) scheme.free-vars()).foldr(linear-set([]), set/(+))

fun new-tvar()
  TVar(ref(Unbound(new-var())))

fun infer(expr : expr) : <st<global>,div,exn,fresh,gamma> ty
  match expr
    Unit -> TUnit
    Var(x) -> 
      match gamma.lookup(x)
        Just(sigma) -> sigma.instantiate()
        Nothing -> throw("unbound variable")
    App(e0, e1) ->
      val tau0 = e0.infer()
      val tau1 = e1.infer()
      val tau' = new-tvar()
      unify(tau0, TFn(tau1, tau'))
      tau'
    Abs(x, e) ->
      val tau = new-tvar()
      with val gamma = gamma.extend(x, Mono(tau))
      val tau' = e.infer()
      TFn(tau, tau')
    Let(x, e0, e1) ->
      val sigma = e0.infer().generalize()
      with val gamma = gamma.extend(x, sigma)
      e1.infer()

fun unify(t1 : ty, t2 : ty)
  match (t1, t2)
    (TUnit, TUnit) -> ()
    (TVar(cell), b) -> 
      match !cell
        Bound(a') -> unify(a', b)
        Unbound(a-id) ->
          if t1 == t2 then () else
            if a-id.occurs-in(b) then throw("occurs check") else
              cell := Bound(b)
    (a, TVar(cell)) ->
      match !cell
        Bound(b') -> unify(a, b')
        Unbound(b-id) ->
          if t1 == t2 then () else
            if b-id.occurs-in(a) then throw("occurs check") else
              cell := Bound(a)
    (TFn(a, b), TFn(c, d)) ->
      unify(a, c)
      unify(b, d)
    _ -> throw("type error")

fun occurs-in(id : int, t : ty)
  match t
    TUnit -> False
    TVar(cell) -> 
      match !cell
        Bound(t') -> id.occurs-in(t')
        Unbound(id') -> id == id'
    TFn(t1, t2) -> id.occurs-in(t1) || id.occurs-in(t2)

fun generalize(t : ty) : <div,gamma,read<global>> ty-scheme
  val to-quantify = t.free-vars() - gamma.free-vars()
  if to-quantify.is-empty then 
    Mono(t)
  else 
    Poly(to-quantify, t)

effect subst
  fun lookup-var(id : int) : maybe<ty>

fun instantiate(scheme : ty-scheme)
  match scheme
    Mono(t) -> t
    Poly(vars, t) -> 
      with fun lookup-var(id) -> 
        if vars.member(id) then 
          Just(new-tvar())
        else 
          Nothing
      t.substitute()

fun substitute(t : ty)
  match t
    TUnit -> TUnit
    TVar(cell) -> 
      match !cell
        Bound(t') -> t'.substitute()
        Unbound(id) ->
          match lookup-var(id)
            Just(new-t) -> new-t.substitute()
            Nothing -> t
    TFn(param, result) -> 
      TFn(param.substitute(), result.substitute())

fun run(expr : expr)
  var counter := 0
  with fun new-var() { counter := counter + 1; counter }
  with val gamma = Env([])
  expr.infer().show().println()


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

  // let-const: \x. let y = \z.x in y: 'a -> 'b -> 'a
  Abs(0, Let(1, Abs(2, Var(0)), Var(1))).run()

