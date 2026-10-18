(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
IMPLEMENTATION MODULE AbiProbe;
FROM SYSTEM IMPORT ADDRESS;
TYPE Buf = POINTER TO ARRAY [0..1023] OF LONGINT;
PROCEDURE M2Add64 (a, b: LONGINT) : LONGINT;
BEGIN RETURN a + b END M2Add64;
PROCEDURE M2SumBuf (buf: ADDRESS; len: CARDINAL) : LONGINT;
VAR p: Buf; i: CARDINAL; s: LONGINT;
BEGIN
  p := buf; s := 0;
  IF len > 0 THEN FOR i := 0 TO len-1 DO s := s + p^[i] END END;
  RETURN s
END M2SumBuf;
END AbiProbe.
