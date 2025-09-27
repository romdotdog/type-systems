module hm-expr

pub type expr
  Unit
  Var(x : int)
  App(e0 : expr, e1 : expr)
  Abs(x : int, e : expr)
  Let(x : int, e0 : expr, e1 : expr)