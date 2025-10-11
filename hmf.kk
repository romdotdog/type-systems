// HMF: Simple Type Inference for First-Class Polymorphism Daan Leijen

// https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/hmf.pdf

module hmf

import std/data/linearset
import std/data/linearmap
import std/test

pub type expr
  Tuple(xs : list<expr>)
  Var(x : int)
  App(e0 : expr, e1 : expr)
  Abs(x : int, e : expr)
  AbsAnn(x : int, alphas : linearSet<int>, scheme : ty-scheme, e : expr)
  Let(x : int, e0 : expr, e1 : expr)

// -- FIGURE 1 --

type ty-ctr
  TFn
  TTuple

fun ty-ctr/(==)(this : ty-ctr, other : ty-ctr) : bool
  match (this, other)
    (TFn, TFn) -> True
    (TTuple, TTuple) -> True
    (_, _) -> False

// unquantified types
type rho-ty
  RCtr(kind : ty-ctr, schemes : list<ty-scheme>)
  RVar(id : int)
  RSkolem(id : int)

fun rho-ty/show(this: rho-ty, left: bool = False): <div,read<global>,exn> string
  match this
    RCtr(TFn, [arg, res]) ->
      val arg-str = match arg
        Rho(r) -> r.show(True)
        Poly -> arg.show()
      val res-str = res.show()
      if left then
        "(" ++ arg-str ++ " -> " ++ res-str ++ ")"
      else
        arg-str ++ " -> " ++ res-str
    RCtr(TTuple, schemes) ->
      "(" ++ schemes.map(show).join(", ") ++ ")"
    RVar(id) ->
      id.show
    RSkolem(id) ->
      "'" ++ id.show

fun rho-ty/(==)(this : rho-ty, other : rho-ty) : <div> bool
  match (this, other)
    (RCtr(kind, schemes), RCtr(kind', schemes')) -> kind == kind' && schemes == schemes'
    (RVar(id), RVar(id')) -> id == id'
    (RSkolem(id), RSkolem(id')) -> id == id'
    (_, _) -> False

fun rho-ty/is-mono(this : rho-ty) : <div> bool
  match this
    RCtr(_, schemes) -> schemes.all(is-mono)
    RVar -> True
    RSkolem -> True

type ty-scheme
  Rho(r : rho-ty)
  Poly(vars : linearSet<int>, rho : rho-ty)

fun ty-scheme/show(this: ty-scheme): <div,read<global>,exn> string
  match this
    Rho(r) -> r.show()
    Poly(vars, rho) ->
      if vars.is-empty then
        rho.show()
      else
        val var-list = vars.list.map(fn(id) id.show).join(" ")
        "∀" ++ var-list ++ ". " ++ rho.show()

fun ty-scheme/(==)(this : ty-scheme, other : ty-scheme) : <div> bool
  match (this, other)
    (Rho(r), Rho(r')) -> r == r'
    (Poly(vars, r), Poly(vars', r')) -> vars == vars' && r == r'
    (_, _) -> False

fun ty-scheme/is-mono(this : ty-scheme) : <div> bool
  match this
    Rho(r) -> r.is-mono()
    Poly -> False

// --------------

effect fresh
  fun new-var() : int

fun new-tvar()
  RVar(new-var())

fun new-skolem()
  RSkolem(new-var())

struct env(vars : list<(int, ty-scheme)>)

fun lookup(env : env, id : int)
  env.vars.lookup fn(id') id == id'

fun extend(env : env, id : int, scheme : ty-scheme)
  Env(Cons((id, scheme), env.vars))

effect val gamma : env

// -- SECTION 4 --

fun rho-ty/free-vars(t : rho-ty) : <div,read<global>> linearSet<int>
  match t
    RVar(id) -> linear-set([id])
    RSkolem -> linear-set([])
    RCtr(_, schemes) -> 
      schemes.map(free-vars).foldl(linear-set([]), set/(+))

fun ty-scheme/free-vars(sigma : ty-scheme) : <div,read<global>> linearSet<int>
  match sigma
    Rho(rho) -> rho.free-vars()
    Poly(vars, rho) -> rho.free-vars() - vars

fun env/free-vars(env : env) : <div,read<global>> linearSet<int>
  env.vars.map(fn((_, scheme)) scheme.free-vars()).foldl(linear-set([]), set/(+))

fun rho-ty/free-skolems(t : rho-ty) : <div,read<global>> linearSet<int>
  match t
    RVar -> linear-set([])
    RSkolem(id) -> linear-set([id])
    RCtr(_, schemes) -> 
      schemes.map(free-skolems).foldl(linear-set([]), set/(+))

fun ty-scheme/free-skolems(sigma : ty-scheme) : <div,read<global>> linearSet<int>
  match sigma
    Rho(rho) -> rho.free-skolems()
    Poly(_, rho) -> rho.free-skolems()

fun list/free-skolems(list : list<ty-scheme>) : <div,read<global>> linearSet<int>
  list.map(fn((scheme)) scheme.free-skolems()).foldl(linear-set([]), set/(+))

// -- SECTION 4.1 --

alias subst = linearMap<int, ty-scheme>

fun rho-ty/substitute(t : rho-ty, subst : subst) : <div> ty-scheme
  match t
    RVar(id) -> 
      match subst.lookup(id)
        Just(new-t) -> new-t
        Nothing -> Rho(t)
    RSkolem -> Rho(t)
    RCtr(kind, schemes) -> 
      Rho(RCtr(kind, schemes.map(fn(s) s.substitute(subst))))

fun ty-scheme/substitute(scheme : ty-scheme, subst : subst) : <div> ty-scheme
  match scheme
    Rho(rho) -> rho.substitute(subst)
    Poly(vars, rho) -> 
      val subst_unbound = subst.remove-all(vars.list)
      match rho.substitute(subst_unbound)
        Rho(rho') -> Poly(vars, rho')
        Poly(vars', rho') -> Poly(vars.union(vars'), rho')
      
fun env/substitute(env : env, subst : subst) : <div> env
  Env(env.vars.map(fn((k, scheme)) (k, scheme.substitute(subst))))

// composition
fun after(post : subst, pre : subst)
  post.union(pre.map(fn(k, v) v.substitute(post)))

// -- FIGURE 5 --

fun mgu(t1 : ty-scheme, t2 : ty-scheme)
  match (t1, t2)
    (Rho(RVar(a-id)), b) -> 
      if t1 == t2 then LinearMap([]) else
        if b.free-vars.member(a-id) then throw("occurs check") else
          LinearMap([(a-id, b)])
    (a, Rho(RVar(b-id))) ->
      if t1 == t2 then LinearMap([]) else
        if a.free-vars.member(b-id) then throw("occurs check") else
          LinearMap([(b-id, a)])
    (Rho(RCtr(kind, schemes)), Rho(RCtr(kind', schemes'))) ->
      if kind != kind' || schemes.length != schemes'.length then throw("type error") else
        schemes.zip(schemes').foldl(LinearMap([]), 
          fn (acc, (s, s')) mgu(s.substitute(acc), s'.substitute(acc)).after(acc))
    (Poly(vars, rho), Poly(vars', rho')) ->
      if vars.length != vars'.length then throw("type error") else
        val skolem-ids = vars.list.zip(vars'.list).map(fn(_) new-var())
        val skolems = skolem-ids.map(fn(id) Rho(RSkolem(id)))
  
        val subst = LinearMap(vars.list.zip(skolems))
        val subst' = LinearMap(vars'.list.zip(skolems))

        val result = mgu(rho.substitute(subst), rho'.substitute(subst'))
        val free-skolems = result.values().free-skolems()
        if skolem-ids.any(fn(sk) free-skolems.member(sk)) then throw("escape check") else
          result
    _ -> throw("type error")

// -- FIGURE 6 --

// instantiate with type vars
fun instantiate(scheme : ty-scheme)
  match scheme
    Rho -> ([], scheme)
    Poly(vars, rho) -> 
      val new-var-ids = vars.list.map(fn(_) new-var())
      val new-vars = new-var-ids.map(fn(id) Rho(RVar(id)))
      val subst = LinearMap(vars.list.zip(new-vars))
      (new-var-ids, rho.substitute(subst))

// instantiate with skolems
fun skolemize(scheme : ty-scheme)
  match scheme
    Rho -> ([], scheme)
    Poly(vars, rho) -> 
      val skolem-ids = vars.list.map(fn(_) new-var())
      val skolems = skolem-ids.map(fn(id) Rho(RSkolem(id)))
      val subst = LinearMap(vars.list.zip(skolems))
      (skolem-ids, rho.substitute(subst))

fun subsume(t1 : ty-scheme, t2 : ty-scheme)
  val (c, rho1) = t1.skolemize()
  val (beta, rho2) = t2.instantiate()
  val result = mgu(rho1, rho2).remove-all(beta)
  val free-skolems = result.values().free-skolems()
  if linear-set(c).common(free-skolems) then throw("escape check") else
    result

// -- FIGURE 8 --

fun funmatch(scheme : ty-scheme) : <fresh,exn> (ty-scheme, ty-scheme, subst)
  match scheme
    Rho(RCtr(TFn, [arg, ret])) -> 
      (arg, ret, LinearMap([]))
    Rho(RVar(id)) ->
      val beta1 = Rho(new-tvar())
      val beta2 = Rho(new-tvar())
      val fn-ty = RCtr(TFn, [beta1, beta2])
      (beta1, beta2, LinearMap([(id, Rho(fn-ty))]))
    _ -> throw("not a function type")

fun generalize(t : ty-scheme) : <div,gamma,read<global>> ty-scheme
  val to-quantify = t.free-vars() - gamma.free-vars()
  if to-quantify.is-empty then 
    t
  else 
    match t
      Rho(r) -> Poly(to-quantify, r)
      Poly(vars, r) -> Poly(vars.union(to-quantify), r)

fun split(s : subst) : <div> (subst, subst)
  val mono = LinearMap(s.list.filter(fn((_, scheme)) scheme.is-mono()))
  val poly = LinearMap(s.list.filter(fn((_, scheme)) !scheme.is-mono()))
  (poly, mono)

// -- FIGURE 7 --

fun instantiate-annot(alphas : linearSet<int>, scheme : ty-scheme)
  val new-var-ids = alphas.list.map(fn(_) new-var())
  val new-vars = new-var-ids.map(fn(id) Rho(RVar(id)))
  val subst = LinearMap(alphas.list.zip(new-vars))
  (new-var-ids, scheme.substitute(subst))

fun infer(expr : expr): <div,gamma,exn,fresh,read<global>,console> (ty-scheme, subst)
  match expr
    Tuple(xs) -> 
      val inferred-xs = xs.map(infer)
      val subst = inferred-xs.foldl(LinearMap([]), fn(acc, (_, subst)) subst.after(acc))
      (Rho(RCtr(TTuple, inferred-xs.map(fst))), subst)
    Var(x) -> 
      match gamma.lookup(x)
        Just(sigma) -> (sigma, LinearMap([]))
        Nothing -> throw("unbound variable")

    // kind of useless
    Let(x, e1, e2) ->
      val (sigma1, theta1) = e1.infer()
      with val gamma = gamma.substitute(theta1).extend(x, sigma1)
      val (sigma2, theta2) = e2.infer()
      (sigma2, theta2.after(theta1))

    Abs(x, e) ->
      val alpha = Rho(new-tvar())
      val (sigma, theta) = (handler { val gamma = gamma.extend(x, alpha) }) fn() e.infer()
      val (_beta, rho) = sigma.instantiate()
      with val gamma = gamma.substitute(theta)
      val result = Rho(RCtr(TFn, [alpha, rho])).substitute(theta)
      (result.generalize(), theta)

    AbsAnn(x, alphas, sigma, e) ->
      val (_new-alphas, body-annotation) = instantiate-annot(alphas, sigma)
      val (body-inferred, theta) = (handler { val gamma = gamma.extend(x, body-annotation) }) fn() e.infer()
      val (_beta, rho) = sigma.instantiate()
      with val gamma = gamma.substitute(theta)
      val result = Rho(RCtr(TFn, [body-inferred, rho])).substitute(theta)
      (result.generalize(), theta)

    App(e1, e2) ->
      val (sigma0, theta0) = e1.infer()
      val (_alpha, rho) = sigma0.instantiate()
      val (sigma1, sigma, theta1) = rho.funmatch()
      with val gamma = gamma.substitute(theta1.after(theta0))
      val (sigma2, theta2) = e2.infer()
      val (big-theta3, theta3) = subsume(sigma1.substitute(theta2), sigma2).split()
      with val gamma = gamma.substitute(theta3.after(theta2))
      if big-theta3.keys().linear-set().common(gamma.free-vars()) then 
        throw("illegal capture")
      else
        val theta4 = theta3.after(theta2).after(theta1).after(theta0)
        (sigma.substitute(big-theta3.after(theta4)).generalize(), theta4)


fun run(expr : expr)
  var counter := 0
  with fun new-var() { counter := counter + 1; counter }
  with val gamma = Env([])
  val (t, s) = expr.infer()
  t.substitute(s).show().println()

pub fun main()
  // basic-id: \x. x  :  a -> a
  Abs(0, Var(0)).run()

  // basic-id (): (\x. x) ()
  App(Abs(0, Var(0)), Tuple([])).run()

  // \x. (\y. y) x
  Abs(0, App(Abs(1, Var(1)), Var(0))).run()

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

