from abstract_syntax import *
from error import *

# Right now just doing normalization, and assuming that
# that procedure is correct!
  # To generate proofs, see what this relies upon

# TODO: Feature where we can declare a ring
  # What theorems are needed?
  # Look at the associative thing
  # Subtraction is annoying, before solving you have to eliminate 
  # or make terms consisten

# TODO: Should this tactic handle intros too?

# TODO: Nicer interfacing for when not solving all the way
  # Specific behavior in `Suffices ? by solve`
  # Or a normalize command for when not in goal-directed mode

var_order = []
var_index = 0

# Meta -> Nat -> bool
def isConst(loc, n):
  return (n in var_order[var_index+1:]) \
          or isNat(n)  \
          or (hasattr(n, 'const_level') and n.const_level > var_index)

# Meta -> Nat -> Nat -> Nat
def addNats(loc, n1, n2):
  x = natToInt(n1)
  y = natToInt(n2)
  ty = n2.typeof
  return intToNat(loc, x + y)

# Meta -> Nat -> Nat -> Nat
def multNats(loc, n1, n2):
  x = natToInt(n1)
  y = natToInt(n2)
  ty = n2.typeof
  return intToNat(loc, x * y)


# Meta -> Term -> Term -> Term
def addConsts(loc, c1, c2):
  if isNat(c1) and isNat(c2):
    return addNats(loc, c1, c2)
  print("retpluss", c1, c2)
  return Call(loc, None, Var(loc, None, '+', []), [c1, c2])

# Meta -> Term -> Term -> Term
def multConsts(loc, c1, c2):
  if isNat(c1) and isNat(c2):
    return multNats(loc, c1, c2)
  print("retcall", c1, c2)
  return Call(loc, None, Var(loc, None, '*', []), [c1, c2])


def make_pc(loc, n):
  global var_index
  global var_order
  if var_index >= len(var_order) - 1:
    return n
  
  var_index += 1
  ret = normalize(loc, n)
  var_index -= 1
  ret.const_level = var_index + 1
  return ret

def make_px(loc, n, x, h):
  assert not isNat(x)
  global var_index
  global var_order
  if var_index < len(var_order) - 1:
    var_index += 1
    n = normalize(loc, n)
    var_index -= 1

  arg2 = Call(loc, None, Var(loc, None, '*', []), [x, h])
  return Call(loc, None, Var(loc, None, '+', []), [n, arg2])


def hplus(loc, f1, f2):
  print(f"hplus({f1}, {f2})", "level:", var_index)

  if isConst(loc, f1) and isConst(loc, f2):
    return make_pc(loc, addConsts(loc, f1, f2))

  if isConst(loc, f1):
    match f2:
      case Call(loc, typeof, rator, [a1, a2]):
        return Call(loc, typeof, rator, [make_pc(loc, addConsts(loc, f1, a1)), a2])
      case _:
        error(loc, "error1 in solve")
  if isConst(loc, f2):
    match f1:
      case Call(loc, typeof, rator, [a1, a2]):
        return Call(loc, typeof, rator, [make_pc(loc, addConsts(loc, f2, a1)), a2])
      case _:
        error(loc, "error2 in solve")
  
  match (f1, f2):
    case (Call(loc1, ty1, r1, [n1, Call(_, _, m, [x1, h1])]), 
          Call(loc2, ty2, r2, [n2, Call(_, _, m2, [x2, h2])])):
      assert x1 == x2
      return make_px(loc, addConsts(loc, n1, n2), x1, hplus(loc, h1, h2))
    case _:
      error(loc, "error3 in solve")


def scal_mult_horner(loc, n, h):
  if isConst(loc, h):
    return make_pc(loc, multConsts(loc, n, h))

  match h:
    case Call(loc1, ty1, r1, [n1, Call(_, _, m, [x1, h1])]):
        return make_px(loc, make_pc(loc, multConsts(loc, n, n1)), x1, scal_mult_horner(loc, n, h1))
    case _:
      error(loc, "h not matched in scal_mult_horner")


def hmult(loc, f1, f2):
  print(f"hmult({f1}, {f2})", "level:", var_index)

  if isConst(loc, f1):
    return scal_mult_horner(loc, f1, f2)

  if isConst(loc, f2):
    return scal_mult_horner(loc, f2, f1)
  

  match (f1, f2):
    case (Call(loc1, ty1, r1, [n1, Call(_, _, m, [x1, h1])]), 
          Call(loc2, ty2, r2, [n2, Call(_, _, m2, [x2, h2])])):
      assert x1 == x2
      return hplus(loc, scal_mult_horner(loc, n1, f2), make_px(loc, intToNat(loc, 0), x1, hmult(loc, h1, f2)))
    case _:
      error(loc, "error3 in solve")


def normalize(loc, formula):
  if isConst(loc, formula): 
    return make_pc(loc, formula)

  match formula:
    case Call(loc, typeof, rator, args):
      op = base_name(rator.name)
      # TODO: Whack because of associativity
      if op == '+':
        a = normalize(loc, args[0])
        for arg in args[1:]:
          a = hplus(loc, a, normalize(loc, arg))
        return a
      elif op == '*':
        return hmult(loc, normalize(loc, args[0]), normalize(loc, args[1]))
      elif op == 'suc':
        return hplus(loc, make_pc(loc, intToNat(loc, 1)), normalize(loc, args[0]))
      else:
        if isConst(loc,formula):
          return make_pc(loc, formula)
        else:
          return make_px(loc, intToNat(loc, 0), formula, make_pc(loc, intToNat(loc, 1)))
    case Mark(loc, ty, subj):
      return normalize(loc, subj)
    case _:
      if isConst(loc, formula): 
        # return formula
        return make_pc(loc, formula)
      else:
        return make_px(loc, intToNat(loc, 0), formula, make_pc(loc, intToNat(loc, 1)))


def discover_free_vars(formula):
  rec_rators = {'+', '*', 'suc', 'zero', '='}
  res = []
  match formula:
    case Call(loc, typeof, rator, args):
      if base_name(rator.name) in rec_rators:
        for a in args:
          vs = discover_free_vars(a)
          for v in vs:
            if v not in res: res.append(v)
      elif formula not in res:
        res.append(formula)
    case Var(loc2, ty2, name, rs):
      if base_name(name) != 'zero':
        if formula not in res: 
          res.append(formula)
    case IfThen(loc, ty, prem, conc):
      for a in [prem, conc]:
        vs = discover_free_vars(a)
        for v in vs:
          if v not in res: res.append(v)
    case Mark(loc, ty, subj):
      return discover_free_vars(subj)
    case _:
      if formula not in res:
        res.append(formula)
  
  return res


# The entry point
def gen_sol(loc, formula, reset= True):
  print(formula)
  global var_order
  global var_index

  if reset:
    var_order = list(discover_free_vars(formula))
    var_index = 0
    print(var_order)
  match formula:
    case Call(loc, typeof, Var(loc2, ty2, '=', rs), args):
      l_red = args[0]
      r_red = args[1]
      
      l_red = normalize(loc, args[0])
      r_red = normalize(loc, args[1])

      print(l_red, "\t",  r_red)

      return Call(loc, typeof, Var(loc2, ty2, '=', rs), [l_red, r_red])
    case IfThen(loc, ty, prem, conc):
      new_prem = gen_sol(loc, prem, False)
      new_conc = gen_sol(loc, conc, False)

      return IfThen(loc, ty, new_prem, new_conc)
    case Bool():
      return formula
    case _:
      set_verbose(True)
      print(formula)
      error(loc, f'con only solve equality, got {formula}')