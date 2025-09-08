import efmc.verifytools.daikon.inv_ast as dast;
import efmc.verifytools.boogie.ast as bast;

def daikonToBoogieExpr(astn):
  if (isinstance(astn, dast.AstUnExpr)):
    cn = daikonToBoogieExpr(astn.expr)
    try:
      boogieOp = {
        '-': '-',
        '!': '!',
      }[astn.op]
      return bast.AstUnExpr(boogieOp, cn)
    except:
      raise Exception("Don't know how to translate " + str(astn))
  elif (isinstance(astn, dast.AstBinExpr)):
    ln,rn = map(daikonToBoogieExpr, [astn.lhs, astn.rhs])

    # We can translate power operators to a constant power
    if (astn.op == "**" and isinstance(astn.rhs, dast.AstNumber)):
      res = ln;
      for _ in range(astn.rhs.num-1):
        res = bast.AstBinExpr(res, '*', ln)
      return res
    else:
      try:
        boogieOp = {
          '&&': '&&',
          '||': '||',
          '==': '==',
          '!=': '!=',
          '<' : '<' ,
          '>' : '>' ,
          '<=': '<=',
          '>=': '>=',
          '+' : '+' ,
          '-' : '-' ,
          '*' : '*' ,
          '/' : '/' ,
          '%' : 'mod',
          '==>' : '==>'
        }[astn.op]
        return bast.AstBinExpr(ln, boogieOp, rn)
      except:
        raise Exception("Don't know how to translate " + str(astn))
  elif (isinstance(astn, dast.AstId)):
    return bast.AstId(astn.name)
  elif (isinstance(astn, dast.AstNumber)):
    return bast.AstNumber(astn.num)
  elif (isinstance(astn, dast.AstTrue)):
    return bast.AstTrue()
  elif (isinstance(astn, dast.AstFalse)):
    return bast.AstFalse()
  elif (isinstance(astn, dast.AstIsOneOf)):
    cn = daikonToBoogieExpr(astn.expr)
    return bast.ast_or([ bast.AstBinExpr(cn, "==", x) for x in
      [ daikonToBoogieExpr(y) for y in astn.options ]
    ])
  elif (isinstance(astn, dast.AstInRange)):
    cn = daikonToBoogieExpr(astn.expr)
    low = astn.lower.num
    hi = astn.upper.num
    return bast.ast_and([
      bast.AstBinExpr(bast.AstNumber(low) , "<=", cn),
      bast.AstBinExpr(cn , "<=", bast.AstNumber(hi))
    ])
  elif (isinstance(astn, dast.AstIsBoolean)):
    cn = daikonToBoogieExpr(astn.expr)
    return bast.ast_or([
        bast.AstBinExpr(cn, "==", bast.AstNumber(0)),
        bast.AstBinExpr(cn, "==", bast.AstNumber(1))
    ])
  elif (isinstance(astn, dast.AstIsEven)):
    cn = daikonToBoogieExpr(astn.expr)
    return bast.AstBinExpr(
        bast.AstBinExpr(cn, "mod", bast.AstNumber(2)),
        "==", bast.AstNumber(0))
  elif (isinstance(astn, dast.AstIsConstMod)):
    expr = daikonToBoogieExpr(astn.expr)
    remainder = daikonToBoogieExpr(astn.remainder)
    modulo = daikonToBoogieExpr(astn.modulo);

    assert modulo.num != 0;

    return bast.AstBinExpr(
        bast.AstBinExpr(expr, "mod", modulo), "==", remainder)
  elif (isinstance(astn, dast.AstHasValues)):
    if (len(astn.values) > 300):
      raise Exception("Can't convert HasValues: Too many options: " +\
                      str(len(astn.values)));
    cn = daikonToBoogieExpr(astn.expr)
    values = list(map(daikonToBoogieExpr, astn.values))
    return bast.ast_or([bast.AstBinExpr(cn, "==", v) for v in values])
  else:
    raise Exception("Don't know how to translate " + str(astn))
