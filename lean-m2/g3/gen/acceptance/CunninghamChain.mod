IMPLEMENTATION MODULE CunninghamChain;
IMPORT LM2Gen;
PROCEDURE FirstKindTerm (p, n: LONGCARD; VAR out: LONGCARD) : INTEGER;
BEGIN
  RETURN LM2Gen.F_CunninghamChain_firstKindTerm(p, n, out)
END FirstKindTerm;
END CunninghamChain.
