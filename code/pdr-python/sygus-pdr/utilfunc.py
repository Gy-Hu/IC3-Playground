
def _get_var(c):
  return set([v for v, _ in c])

def _get_cubes_with_fewer_var(cubes, vset):
  # sort based on variable
  return [dict(cube) for cube in cubes if _get_var(cube).issubset(vset)]

def _get_cubes_with_more_var(cubes, vset):
  # sort based on variable
  return [dict(cube) for cube in cubes if _get_var(cube).issuperset(vset)]


def _get_unified_width(v): # bool 0, bv ... 
  if v.get_type().is_bool_type():
    return 0
  assert (v.get_type().is_bv_type())
  return v.bv_width()

def _to_type_string(v):
  if v.get_type().is_bool_type():
    return 'Bool'
  assert (v.get_type().is_bv_type())
  return ('(_ BitVec %d)' % v.bv_width())

def _to_name_type(v): # v should be a pysmt v
  assert (v.is_symbol())
  return '('+v.symbol_name() + " " + _to_type_string(v)+')'

def _to_name_type_suffix_no_p(v, suffix): # v should be a pysmt v
  assert (v.is_symbol())
  return v.symbol_name() + suffix + " " + _to_type_string(v)

def _to_args(vl):
  return '('+ (' '.join([_to_name_type(v) for v in vl])) + ')'

def _to_tr_args(vl, vp):
  return '('+ (' '.join([_to_name_type(v) for v in vl] + [_to_name_type(v) for v in vp])) + ')'

def _const_to_str(fn):
  if fn.is_bv_constant():
    return '#b' + fn.bv_str()
  elif fn.is_bool_constant():
    return 'true' if fn.is_true() else 'false'
  assert (False) # unknown type

def _gen_smt2(fn):
  return fn.to_smtlib(daggify = Config_smtlib2_daggify)
  
