const

  NODE_NUM : 2;

type

  NODE : 1..NODE_NUM;

  OTHER : enum {Other};

  CACHE_STATE : enum {I, S, E};

  CACHE : record
    State : CACHE_STATE;
  end;

  MSG_CMD: enum {Empty, ReqS, ReqE, Inv, InvAck, GntS, GntE};

  MSG : record
    Cmd : MSG_CMD;
  end;

var

  Cache : array [NODE] of CACHE;
  Chan1 : array [NODE] of MSG;
  Chan2 : array [NODE] of MSG;
  Chan3 : array [NODE] of MSG;
  InvSet : array [NODE] of boolean;
  ShrSet : array [NODE] of boolean;
  ExGntd : boolean;
  CurCmd : MSG_CMD;

startstate "Init"
begin
  for i : NODE do
    Chan1[i].Cmd := Empty;
    Chan2[i].Cmd := Empty;
    Chan3[i].Cmd := Empty;
    Cache[i].State := I;
    InvSet[i] := false;
    ShrSet[i] := false;
  end;
  ExGntd := false;
  CurCmd := Empty;
endstartstate;

ruleset i : NODE do
rule "RecvGntE"
  Chan2[i].Cmd = GntE
==>
begin
  Cache[i].State := E;
  Chan2[i].Cmd := Empty;
endrule;
endruleset;

ruleset i : NODE do
rule "RecvGntS"
  Chan2[i].Cmd = GntS
==>
begin
  Cache[i].State := S;
  Chan2[i].Cmd := Empty;
endrule;
endruleset;

ruleset i : NODE do
rule "SendGntE"
  CurCmd = ReqE &
  Chan2[i].Cmd = Empty &
  ExGntd = false &
  forall j : NODE do
    ShrSet[j] = false
  end
==>
begin
  Chan2[i].Cmd := GntE;
  ShrSet[i] := true;
  ExGntd := true;
  CurCmd := Empty;
endrule;
endruleset;

ruleset i : NODE do
rule "SendGntS"
  CurCmd = ReqS &
  Chan2[i].Cmd = Empty &
  ExGntd = false
==>
begin
  Chan2[i].Cmd := GntS;
  ShrSet[i] := true;
  CurCmd := Empty;
endrule;
endruleset;

ruleset i : NODE do
rule "RecvInvAck1"
  Chan3[i].Cmd = InvAck &
  CurCmd != Empty &
  ExGntd = true
==>
begin
  Chan3[i].Cmd := Empty;
  ShrSet[i] := false;
  ExGntd := false;
endrule;
endruleset;

ruleset i : NODE do
rule "RecvInvAck2"
  Chan3[i].Cmd = InvAck &
  CurCmd != Empty &
  ExGntd = false
==>
begin
  Chan3[i].Cmd := Empty;
  ShrSet[i] := false;
endrule;
endruleset;

ruleset i : NODE do
rule "SendInvAck"
  Chan2[i].Cmd = Inv &
  Chan3[i].Cmd = Empty
==>
begin
  Chan2[i].Cmd := Empty;
  Chan3[i].Cmd := InvAck;
  Cache[i].State := I;
endrule;
endruleset;

ruleset i : NODE do
rule "SendInv"
  Chan2[i].Cmd = Empty &
  InvSet[i] = true &
  ( CurCmd = ReqE | CurCmd = ReqS & ExGntd = true )
==>
begin
  Chan2[i].Cmd := Inv;
  InvSet[i] := false;
endrule;
endruleset;

ruleset i : NODE do
rule "RecvReqE"
  CurCmd = Empty &
  Chan1[i].Cmd = ReqE
==>
begin
  CurCmd := ReqE;
  Chan1[i].Cmd := Empty;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  end;
endrule;
endruleset;

ruleset i : NODE do
rule "RecvReqS"
  CurCmd = Empty &
  Chan1[i].Cmd = ReqS
==>
begin
  CurCmd := ReqS;
  Chan1[i].Cmd := Empty;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  end;
endrule;
endruleset;

ruleset i : NODE do
rule "SendReqE"
  Chan1[i].Cmd = Empty &
  (Cache[i].State = I | Cache[i].State = S)
==>
begin
  Chan1[i].Cmd := ReqE;
endrule;
endruleset;

ruleset i : NODE do
rule "SendReqS"
  Chan1[i].Cmd = Empty &
  Cache[i].State = I
==>
begin
  Chan1[i].Cmd := ReqS;
endrule;
endruleset;
invariant "deadlock_RecvGntS1_1_RecvGntE2_1_SendGntE2_1_RecvInvAck21_1_SendGntS1_1_RecvInvAck12_1_SendInvAck1_1_SendInvAck2_1_SendInv1_1_SendInv2_1_RecvReqE1"
   !(ExGntd = true & ShrSet[2] = true);