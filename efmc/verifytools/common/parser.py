#pylint: disable=unused-argument, no-self-argument
class Parser:
    pass

class InfixExprParser(Parser):
  def onAtom(s, prod, st, loc, toks):
      raise Exception("NYI")
  def onUnaryOp(s, prod, st, loc, toks):
      raise Exception("NYI")
  def onLABinOp(s, prod, st, loc, toks):
      raise Exception("NYI")
  def onRABinOp(s, prod, st, loc, toks):
      raise Exception("NYI")
  def onNABinOp(s, prod, st, loc, toks):
      raise Exception("NYI")

