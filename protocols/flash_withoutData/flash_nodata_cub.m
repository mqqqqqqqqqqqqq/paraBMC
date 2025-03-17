
const

  NODE_NUM : 1;

type

  NODE : scalarset(NODE_NUM);

  CACHE_STATE : enum {CACHE_I, CACHE_S, CACHE_E};

  NODE_CMD : enum {NODE_None, NODE_Get, NODE_GetX};

  NODE_STATE : record
    ProcCmd : NODE_CMD;
    InvMarked : boolean;
    CacheState : CACHE_STATE;
  end;

  DIR_STATE : record
    Pending : boolean;
    Local : boolean;
    Dirty : boolean;
    HeadVld : boolean;
    HeadPtr : NODE;
    HomeHeadPtr : boolean;
    ShrVld : boolean;
    ShrSet : array [NODE] of boolean;
    HomeShrSet : boolean;
    InvSet : array [NODE] of boolean;
    HomeInvSet : boolean;
  end;

  UNI_CMD : enum {UNI_None, UNI_Get, UNI_GetX, UNI_Put, UNI_PutX, UNI_Nak};

  UNI_MSG : record
    Cmd : UNI_CMD;
    Proc : NODE;
    HomeProc : boolean;
  end;

  INV_CMD : enum {INV_None, INV_Inv, INV_InvAck};

  INV_MSG : record
    Cmd : INV_CMD;
  end;

  RP_CMD : enum {RP_None, RP_Replace};

  RP_MSG : record
    Cmd : RP_CMD;
  end;

  WB_CMD : enum {WB_None, WB_Wb};

  WB_MSG : record
    Cmd : WB_CMD;
    Proc : NODE;
    HomeProc : boolean;
  end;

  SHWB_CMD : enum {SHWB_None, SHWB_ShWb, SHWB_FAck};

  SHWB_MSG : record
    Cmd : SHWB_CMD;
    Proc : NODE;
    HomeProc : boolean;
  end;

  NAKC_CMD : enum {NAKC_None, NAKC_Nakc};

  NAKC_MSG : record
    Cmd : NAKC_CMD;
  end;

  STATE : record
    Proc : array [NODE] of NODE_STATE;
    HomeProc : NODE_STATE;
    Dir : DIR_STATE;
    UniMsg : array [NODE] of UNI_MSG;
    HomeUniMsg : UNI_MSG;
    InvMsg : array [NODE] of INV_MSG;
    HomeInvMsg : INV_MSG;
    RpMsg : array [NODE] of RP_MSG;
    HomeRpMsg : RP_MSG;
    WbMsg : WB_MSG;
    ShWbMsg : SHWB_MSG;
    NakcMsg : NAKC_MSG;
  end;

var

  Sta : STATE;


ruleset i : NODE do
startstate "Init"
  Sta.Dir.Pending := false;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := false;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := true;
  Sta.Dir.ShrVld := false;
  Sta.WbMsg.Cmd := WB_None;
  Sta.WbMsg.Proc := i;
  Sta.WbMsg.HomeProc := true;
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.ShWbMsg.Proc := i;
  Sta.ShWbMsg.HomeProc := true;
  Sta.NakcMsg.Cmd := NAKC_None;
  for j : NODE do
    Sta.Proc[j].ProcCmd := NODE_None;
    Sta.Proc[j].InvMarked := false;
    Sta.Proc[j].CacheState := CACHE_I;
    Sta.Dir.ShrSet[j] := false;
    Sta.Dir.InvSet[j] := false;
    Sta.UniMsg[j].Cmd := UNI_None;
    Sta.UniMsg[j].Proc := i;
    Sta.UniMsg[j].HomeProc := true;
    Sta.InvMsg[j].Cmd := INV_None;
    Sta.RpMsg[j].Cmd := RP_None;
  end;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeUniMsg.Cmd := UNI_None;
  Sta.HomeUniMsg.Proc := i;
  Sta.HomeUniMsg.HomeProc := true;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.HomeRpMsg.Cmd := RP_None;
endstartstate;
endruleset;




ruleset i : NODE do
rule "PI_Remote_Get"
  Sta.Proc[i].ProcCmd = NODE_None &
  Sta.Proc[i].CacheState = CACHE_I
==>
begin
  Sta.Proc[i].ProcCmd := NODE_Get;
  Sta.UniMsg[i].Cmd := UNI_Get;
  Sta.UniMsg[i].HomeProc := true;
endrule;
endruleset;

rule "PI_Local_Get_Get"
  Sta.HomeProc.ProcCmd = NODE_None &
  Sta.HomeProc.CacheState = CACHE_I &
  Sta.Dir.Pending = false & Sta.Dir.Dirty = true
==>
begin
  Sta.HomeProc.ProcCmd := NODE_Get;
  Sta.Dir.Pending := true;
  Sta.HomeUniMsg.Cmd := UNI_Get;
  Sta.HomeUniMsg.Proc := Sta.Dir.HeadPtr;
  Sta.HomeUniMsg.HomeProc := Sta.Dir.HomeHeadPtr;
endrule;

rule "PI_Local_Get_Put"
  Sta.HomeProc.ProcCmd = NODE_None &
  Sta.HomeProc.CacheState = CACHE_I &
  Sta.Dir.Pending = false & Sta.Dir.Dirty = false
==>
begin
  Sta.Dir.Local := true;
  Sta.HomeProc.ProcCmd := NODE_None;
  if (Sta.HomeProc.InvMarked = true) then
    Sta.HomeProc.InvMarked := false;
    Sta.HomeProc.CacheState := CACHE_I;
  else
    Sta.HomeProc.CacheState := CACHE_S;
  end;
endrule;

ruleset i : NODE do
rule "PI_Remote_GetX"
  Sta.Proc[i].ProcCmd = NODE_None &
  Sta.Proc[i].CacheState = CACHE_I
==>
begin
  Sta.Proc[i].ProcCmd := NODE_GetX;
  Sta.UniMsg[i].Cmd := UNI_GetX;
  Sta.UniMsg[i].HomeProc := true;
endrule;
endruleset;

rule "PI_Local_GetX_GetX"
  Sta.HomeProc.ProcCmd = NODE_None &
  ( Sta.HomeProc.CacheState = CACHE_I |
    Sta.HomeProc.CacheState = CACHE_S ) &
  Sta.Dir.Pending = false & Sta.Dir.Dirty = true
==>
begin
  Sta.HomeProc.ProcCmd := NODE_GetX;
  Sta.Dir.Pending := true;
  Sta.HomeUniMsg.Cmd := UNI_GetX;
  Sta.HomeUniMsg.Proc := Sta.Dir.HeadPtr;
  Sta.HomeUniMsg.HomeProc := Sta.Dir.HomeHeadPtr;
endrule;

rule "PI_Local_GetX_PutX_HeadVld"
  Sta.HomeProc.ProcCmd = NODE_None &
  ( Sta.HomeProc.CacheState = CACHE_I |
    Sta.HomeProc.CacheState = CACHE_S ) &
  Sta.Dir.Pending = false & Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true
==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;

  Sta.Dir.Pending := true;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;

  for i : NODE do
    Sta.Dir.ShrSet[i] := false;
    if ( Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[i] = true |
           Sta.Dir.HeadPtr = i & Sta.Dir.HomeHeadPtr = false ) then
      Sta.Dir.InvSet[i] := true;
      Sta.InvMsg[i].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[i] := false;
      Sta.InvMsg[i].Cmd := INV_None;
    end;
  end;

  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;

  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_E;
endrule;

rule "PI_Local_GetX_PutX"
  Sta.HomeProc.ProcCmd = NODE_None &
  ( Sta.HomeProc.CacheState = CACHE_I |
    Sta.HomeProc.CacheState = CACHE_S ) &
  Sta.Dir.Pending = false & Sta.Dir.Dirty = false & Sta.Dir.HeadVld = false
==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;

  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_E;
endrule;

ruleset i : NODE do
rule "PI_Remote_PutX"
  Sta.Proc[i].ProcCmd = NODE_None &
  Sta.Proc[i].CacheState = CACHE_E
==>
begin
  Sta.Proc[i].CacheState := CACHE_I;
  Sta.WbMsg.Cmd := WB_Wb;
  Sta.WbMsg.Proc := i;
  Sta.WbMsg.HomeProc := false;
endrule;
endruleset;

rule "PI_Local_PutX"
  Sta.HomeProc.ProcCmd = NODE_None &
  Sta.HomeProc.CacheState = CACHE_E
==>
begin
  if (Sta.Dir.Pending = true) then
    Sta.HomeProc.CacheState := CACHE_I;
    Sta.Dir.Dirty := false;
  else
    Sta.HomeProc.CacheState := CACHE_I;
    Sta.Dir.Local := false;
    Sta.Dir.Dirty := false;
  end;
endrule;

ruleset i : NODE do
rule "PI_Remote_Replace"
  Sta.Proc[i].ProcCmd = NODE_None &
  Sta.Proc[i].CacheState = CACHE_S
==>
begin
  Sta.Proc[i].CacheState := CACHE_I;
  Sta.RpMsg[i].Cmd := RP_Replace;
endrule;
endruleset;

rule "PI_Local_Replace"
  Sta.HomeProc.ProcCmd = NODE_None &
  Sta.HomeProc.CacheState = CACHE_S
==>
begin
  Sta.Dir.Local := false;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;

ruleset i : NODE do
rule "NI_Nak"
  Sta.UniMsg[i].Cmd = UNI_Nak
==>
begin
  Sta.UniMsg[i].Cmd := UNI_None;
  Sta.Proc[i].ProcCmd := NODE_None;
  Sta.Proc[i].InvMarked := false;
endrule;
endruleset;

rule "NI_Nak_Home"
  Sta.HomeUniMsg.Cmd = UNI_Nak
==>
begin
  Sta.HomeUniMsg.Cmd := UNI_None;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
endrule;

rule "NI_Nak_Clear"
  Sta.NakcMsg.Cmd = NAKC_Nakc
==>
begin
  Sta.NakcMsg.Cmd := NAKC_None;
  Sta.Dir.Pending := false;
endrule;

ruleset i : NODE do
rule "NI_Local_Get_Nak"
  Sta.UniMsg[i].Cmd = UNI_Get &
  Sta.UniMsg[i].HomeProc = true &
  Sta.RpMsg[i].Cmd != RP_Replace &
  ( Sta.Dir.Pending = true |
    Sta.Dir.Dirty = true & Sta.Dir.Local = true & Sta.HomeProc.CacheState != CACHE_E |
    Sta.Dir.Dirty = true & Sta.Dir.Local = false & Sta.Dir.HeadPtr = i & Sta.Dir.HomeHeadPtr = false)
==>
begin
  Sta.UniMsg[i].Cmd := UNI_Nak;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_Get_Get"
  Sta.UniMsg[i].Cmd = UNI_Get &
  Sta.UniMsg[i].HomeProc = true &
  Sta.RpMsg[i].Cmd != RP_Replace &
  Sta.Dir.Pending = false & Sta.Dir.Dirty = true & Sta.Dir.Local = false &
  (Sta.Dir.HeadPtr != i | Sta.Dir.HomeHeadPtr = true)
==>
begin
  Sta.Dir.Pending := true;
  Sta.UniMsg[i].Cmd := UNI_Get;
  Sta.UniMsg[i].Proc := Sta.Dir.HeadPtr;
  Sta.UniMsg[i].HomeProc := Sta.Dir.HomeHeadPtr;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_Get_Put_Head"
  Sta.UniMsg[i].Cmd = UNI_Get &
  Sta.UniMsg[i].HomeProc = true &
  Sta.RpMsg[i].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true
==>
begin
  Sta.Dir.ShrVld := true;
  Sta.Dir.ShrSet[i] := true;
  for j : NODE do
    if (j = i)  then
      Sta.Dir.InvSet[j] := true;
    else
      Sta.Dir.InvSet[j] := Sta.Dir.ShrSet[j];
    end;
  end;
  Sta.Dir.HomeInvSet := Sta.Dir.HomeShrSet;
  Sta.UniMsg[i].Cmd := UNI_Put;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_Get_Put"
  Sta.UniMsg[i].Cmd = UNI_Get &
  Sta.UniMsg[i].HomeProc = true &
  Sta.RpMsg[i].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadVld = false
==>
begin
    Sta.Dir.HeadVld := true;
    Sta.Dir.HeadPtr := i;
    Sta.Dir.HomeHeadPtr := false;
    Sta.UniMsg[i].Cmd := UNI_Put;
endrule;
endruleset;


ruleset i : NODE do
rule "NI_Local_Get_Put_Dirty"
  Sta.UniMsg[i].Cmd = UNI_Get &
  Sta.UniMsg[i].HomeProc = true &
  Sta.RpMsg[i].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true & Sta.Dir.Local = true & Sta.HomeProc.CacheState = CACHE_E
==>
begin
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.HomeProc.CacheState := CACHE_S;
  Sta.UniMsg[i].Cmd := UNI_Put;
endrule;
endruleset;

ruleset i : NODE; j : NODE do
rule "NI_Remote_Get_Nak"
  i != j &
  Sta.UniMsg[i].Cmd = UNI_Get &
  Sta.UniMsg[i].Proc = j & Sta.UniMsg[i].HomeProc = false &
  Sta.Proc[j].CacheState != CACHE_E
==>
begin
  Sta.UniMsg[i].Cmd := UNI_Nak;
  Sta.NakcMsg.Cmd := NAKC_Nakc;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Remote_Get_Nak_Home"
  Sta.HomeUniMsg.Cmd = UNI_Get &
  Sta.HomeUniMsg.Proc = i & Sta.HomeUniMsg.HomeProc = false &
  Sta.Proc[i].CacheState != CACHE_E
==>
begin
  Sta.HomeUniMsg.Cmd := UNI_Nak;
  Sta.NakcMsg.Cmd := NAKC_Nakc;
endrule;
endruleset;

ruleset i : NODE; j : NODE do
rule "NI_Remote_Get_Put"
  i != j &
  Sta.UniMsg[i].Cmd = UNI_Get &
  Sta.UniMsg[i].Proc = j & Sta.UniMsg[i].HomeProc = false &
  Sta.Proc[j].CacheState = CACHE_E
==>
begin
  Sta.Proc[j].CacheState := CACHE_S;
  Sta.UniMsg[i].Cmd := UNI_Put;
  Sta.ShWbMsg.Cmd := SHWB_ShWb;
  Sta.ShWbMsg.Proc := i;
  Sta.ShWbMsg.HomeProc := false;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Remote_Get_Put_Home"
  Sta.HomeUniMsg.Cmd = UNI_Get &
  Sta.HomeUniMsg.Proc = i & Sta.HomeUniMsg.HomeProc = false &
  Sta.Proc[i].CacheState = CACHE_E
==>
begin
  Sta.Proc[i].CacheState := CACHE_S;
  Sta.HomeUniMsg.Cmd := UNI_Put;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_GetX_Nak"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  ( Sta.Dir.Pending = true |
    Sta.Dir.Dirty = true & Sta.Dir.Local = true & Sta.HomeProc.CacheState != CACHE_E |
    Sta.Dir.Dirty = true & Sta.Dir.Local = false & Sta.Dir.HeadPtr = i & Sta.Dir.HomeHeadPtr = false)
==>
begin
  Sta.UniMsg[i].Cmd := UNI_Nak;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_GetX_GetX"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false & Sta.Dir.Dirty = true & Sta.Dir.Local = false &
  (Sta.Dir.HeadPtr != i | Sta.Dir.HomeHeadPtr = true)
==>
begin
  Sta.Dir.Pending := true;
  Sta.UniMsg[i].Cmd := UNI_GetX;
  Sta.UniMsg[i].Proc := Sta.Dir.HeadPtr;
  Sta.UniMsg[i].HomeProc := Sta.Dir.HomeHeadPtr;
endrule;
endruleset;


ruleset i : NODE do
rule "NI_Local_GetX_PutX_1"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadVld = false & Sta.Dir.Local = true & Sta.HomeProc.ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for j : NODE do
    Sta.Dir.ShrSet[j] := false;
    Sta.Dir.InvSet[j] := false;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.UniMsg[i].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.HomeProc.InvMarked := true;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_GetX_PutX_2"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadVld = false & Sta.Dir.Local = true & Sta.HomeProc.ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for j : NODE do
    Sta.Dir.ShrSet[j] := false;
    Sta.Dir.InvSet[j] := false;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.UniMsg[i].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_GetX_PutX_3"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadVld = false & Sta.Dir.Local = false
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for j : NODE do
    Sta.Dir.ShrSet[j] := false;
    Sta.Dir.InvSet[j] := false;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.UniMsg[i].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_GetX_PutX_4"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadPtr = i & Sta.Dir.HomeHeadPtr = false & Sta.Dir.HomeShrSet = false &
  forall j : NODE do j != i -> Sta.Dir.ShrSet[j] = false end &
  Sta.Dir.Local = true & Sta.HomeProc.ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for j : NODE do
    Sta.Dir.ShrSet[j] := false;
    Sta.Dir.InvSet[j] := false;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.UniMsg[i].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.HomeProc.InvMarked := true;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_GetX_PutX_5"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadPtr = i & Sta.Dir.HomeHeadPtr = false & Sta.Dir.HomeShrSet = false &
  forall j : NODE do j != i -> Sta.Dir.ShrSet[j] = false end &
  Sta.Dir.Local = true & Sta.HomeProc.ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for j : NODE do
    Sta.Dir.ShrSet[j] := false;
    Sta.Dir.InvSet[j] := false;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.UniMsg[i].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_GetX_PutX_6"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadPtr = i & Sta.Dir.HomeHeadPtr = false & Sta.Dir.HomeShrSet = false &
  forall j : NODE do j != i -> Sta.Dir.ShrSet[j] = false end &
  Sta.Dir.Local = false
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for j : NODE do
    Sta.Dir.ShrSet[j] := false;
    Sta.Dir.InvSet[j] := false;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.UniMsg[i].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_GetX_PutX_7"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true & (Sta.Dir.HeadPtr != i | Sta.Dir.HomeHeadPtr = true) &
  Sta.Dir.Local = true & Sta.HomeProc.ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for j : NODE do
    Sta.Dir.ShrSet[j] := false;
    if ( j != i &
         ( Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[j] = true |
           Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = j & Sta.Dir.HomeHeadPtr = false) ) then
      Sta.Dir.InvSet[j] := true;
      Sta.InvMsg[j].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[j] := false;
      Sta.InvMsg[j].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.UniMsg[i].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_GetX_PutX_7_NODE_Get"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true & (Sta.Dir.HeadPtr != i | Sta.Dir.HomeHeadPtr = true) &
  Sta.Dir.Local = true & Sta.HomeProc.ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for j : NODE do
    Sta.Dir.ShrSet[j] := false;
    if ( j != i &
         ( Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[j] = true |
           Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = j & Sta.Dir.HomeHeadPtr = false) ) then
      Sta.Dir.InvSet[j] := true;
      Sta.InvMsg[j].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[j] := false;
      Sta.InvMsg[j].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.UniMsg[i].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.HomeProc.InvMarked := true;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_GetX_PutX_8_Home"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = i & Sta.Dir.HomeHeadPtr = false &
  Sta.Dir.HomeShrSet = true &
  Sta.Dir.Local = true & Sta.HomeProc.ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for j : NODE do
    Sta.Dir.ShrSet[j] := false;
    if ( j != i &
         ( Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[j] = true |
           Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = j & Sta.Dir.HomeHeadPtr = false) ) then
      Sta.Dir.InvSet[j] := true;
      Sta.InvMsg[j].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[j] := false;
      Sta.InvMsg[j].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.UniMsg[i].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_GetX_PutX_8_Home_NODE_Get"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = i & Sta.Dir.HomeHeadPtr = false &
  Sta.Dir.HomeShrSet = true &
  Sta.Dir.Local = true & Sta.HomeProc.ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for j : NODE do
    Sta.Dir.ShrSet[j] := false;
    if ( j != i &
         ( Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[j] = true |
           Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = j & Sta.Dir.HomeHeadPtr = false) ) then
      Sta.Dir.InvSet[j] := true;
      Sta.InvMsg[j].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[j] := false;
      Sta.InvMsg[j].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.UniMsg[i].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.HomeProc.InvMarked := true;
endrule;
endruleset;

ruleset i : NODE; j : NODE do
rule "NI_Local_GetX_PutX_8"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = i & Sta.Dir.HomeHeadPtr = false &
  Sta.Dir.ShrSet[j] = true &
  Sta.Dir.Local = true & Sta.HomeProc.ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ( p != i &
         ( Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true |
           Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p & Sta.Dir.HomeHeadPtr = false) ) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.UniMsg[i].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset i : NODE; j : NODE do
rule "NI_Local_GetX_PutX_8_NODE_Get"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = i & Sta.Dir.HomeHeadPtr = false &
  Sta.Dir.ShrSet[j] = true &
  Sta.Dir.Local = true & Sta.HomeProc.ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ( p != i &
         ( Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true |
           Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p & Sta.Dir.HomeHeadPtr = false) ) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;
  Sta.UniMsg[i].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
  Sta.HomeProc.InvMarked := true;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_GetX_PutX_9"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true & (Sta.Dir.HeadPtr != i | Sta.Dir.HomeHeadPtr = true) &
  Sta.Dir.Local = false
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for j : NODE do
    Sta.Dir.ShrSet[j] := false;
    if ( j != i &
         ( Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[j] = true |
           Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = j & Sta.Dir.HomeHeadPtr = false) ) then
      Sta.Dir.InvSet[j] := true;
      Sta.InvMsg[j].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[j] := false;
      Sta.InvMsg[j].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;

  Sta.UniMsg[i].Cmd := UNI_PutX;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_GetX_PutX_10_Home"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = i & Sta.Dir.HomeHeadPtr = false &
  Sta.Dir.HomeShrSet = true &
  Sta.Dir.Local = false
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for j : NODE do
    Sta.Dir.ShrSet[j] := false;
    if ( j != i &
         ( Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[j] = true |
           Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = j & Sta.Dir.HomeHeadPtr = false) ) then
      Sta.Dir.InvSet[j] := true;
      Sta.InvMsg[j].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[j] := false;
      Sta.InvMsg[j].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;

  Sta.UniMsg[i].Cmd := UNI_PutX;
endrule;
endruleset;

ruleset i : NODE; j : NODE do
rule "NI_Local_GetX_PutX_10"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = i & Sta.Dir.HomeHeadPtr = false &
  Sta.Dir.ShrSet[j] = true &
  Sta.Dir.Local = false
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    if ( p != i &
         ( Sta.Dir.ShrVld = true & Sta.Dir.ShrSet[p] = true |
           Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = p & Sta.Dir.HomeHeadPtr = false) ) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    end;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.HomeInvMsg.Cmd := INV_None;

  Sta.UniMsg[i].Cmd := UNI_PutX;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Local_GetX_PutX_11"
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].HomeProc = true &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true & Sta.Dir.Local = true & Sta.HomeProc.CacheState = CACHE_E
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := i;
  Sta.Dir.HomeHeadPtr := false;
  Sta.Dir.ShrVld := false;
  for j : NODE do
    Sta.Dir.ShrSet[j] := false;
    Sta.Dir.InvSet[j] := false;
  end;
  Sta.Dir.HomeShrSet := false;
  Sta.Dir.HomeInvSet := false;
  Sta.UniMsg[i].Cmd := UNI_PutX;
  Sta.HomeProc.CacheState := CACHE_I;
endrule;
endruleset;

ruleset i : NODE; j : NODE do
rule "NI_Remote_GetX_Nak"
  i != j &
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].Proc = j & Sta.UniMsg[i].HomeProc = false &
  Sta.Proc[j].CacheState != CACHE_E
==>
begin
  Sta.UniMsg[i].Cmd := UNI_Nak;
  Sta.NakcMsg.Cmd := NAKC_Nakc;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Remote_GetX_Nak_Home"
  Sta.HomeUniMsg.Cmd = UNI_GetX &
  Sta.HomeUniMsg.Proc = i & Sta.HomeUniMsg.HomeProc = false &
  Sta.Proc[i].CacheState != CACHE_E
==>
begin
  Sta.HomeUniMsg.Cmd := UNI_Nak;
  Sta.NakcMsg.Cmd := NAKC_Nakc;
endrule;
endruleset;

ruleset i : NODE; j : NODE do
rule "NI_Remote_GetX_PutX"
  i != j &
  Sta.UniMsg[i].Cmd = UNI_GetX &
  Sta.UniMsg[i].Proc = j & Sta.UniMsg[i].HomeProc = false &
  Sta.Proc[j].CacheState = CACHE_E
==>
begin
  Sta.Proc[j].CacheState := CACHE_I;
  Sta.UniMsg[i].Cmd := UNI_PutX;
  Sta.ShWbMsg.Cmd := SHWB_FAck;
  Sta.ShWbMsg.Proc := i;
  Sta.ShWbMsg.HomeProc := false;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Remote_GetX_PutX_Home"
  Sta.HomeUniMsg.Cmd = UNI_GetX &
  Sta.HomeUniMsg.Proc = i & Sta.HomeUniMsg.HomeProc = false &
  Sta.Proc[i].CacheState = CACHE_E
==>
begin
  Sta.Proc[i].CacheState := CACHE_I;
  Sta.HomeUniMsg.Cmd := UNI_PutX;
endrule;
endruleset;

rule "NI_Local_Put"
  Sta.HomeUniMsg.Cmd = UNI_Put
==>
begin
  Sta.HomeUniMsg.Cmd := UNI_None;
  Sta.Dir.Pending := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.Local := true;
  Sta.HomeProc.ProcCmd := NODE_None;
  if (Sta.HomeProc.InvMarked = true) then
    Sta.HomeProc.InvMarked := false;
    Sta.HomeProc.CacheState := CACHE_I;
  else
    Sta.HomeProc.CacheState := CACHE_S;
  end;
endrule;

ruleset i : NODE do
rule "NI_Remote_Put"
  Sta.UniMsg[i].Cmd = UNI_Put
==>
begin
  Sta.UniMsg[i].Cmd := UNI_None;
  Sta.Proc[i].ProcCmd := NODE_None;
  if (Sta.Proc[i].InvMarked = true) then
    Sta.Proc[i].InvMarked := false;
    Sta.Proc[i].CacheState := CACHE_I;
  else
    Sta.Proc[i].CacheState := CACHE_S;
  end;
endrule;
endruleset;

rule "NI_Local_PutXAcksDone"
  Sta.HomeUniMsg.Cmd = UNI_PutX
==>
begin
  Sta.HomeUniMsg.Cmd := UNI_None;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := true;
  Sta.Dir.HeadVld := false;
  Sta.HomeProc.ProcCmd := NODE_None;
  Sta.HomeProc.InvMarked := false;
  Sta.HomeProc.CacheState := CACHE_E;
endrule;

ruleset i : NODE do
rule "NI_Remote_PutX"
  Sta.UniMsg[i].Cmd = UNI_PutX &
  Sta.Proc[i].ProcCmd = NODE_GetX
==>
begin
  Sta.UniMsg[i].Cmd := UNI_None;
  Sta.Proc[i].ProcCmd := NODE_None;
  Sta.Proc[i].InvMarked := false;
  Sta.Proc[i].CacheState := CACHE_E;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_Inv"
  Sta.InvMsg[i].Cmd = INV_Inv
==>
begin
  Sta.InvMsg[i].Cmd := INV_InvAck;
  Sta.Proc[i].CacheState := CACHE_I;
  if (Sta.Proc[i].ProcCmd = NODE_Get) then
    Sta.Proc[i].InvMarked := true;
  end;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_InvAck_exists_Home"
  Sta.InvMsg[i].Cmd = INV_InvAck &
  Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true &
  Sta.Dir.HomeInvSet = true
==>
begin
  Sta.InvMsg[i].Cmd := INV_None;
  Sta.Dir.InvSet[i] := false;
endrule;
endruleset;

ruleset i : NODE; j : NODE do
rule "NI_InvAck_exists"
  Sta.InvMsg[i].Cmd = INV_InvAck &
  Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true &
  (j != i & Sta.Dir.InvSet[j] = true)
==>
begin
  Sta.InvMsg[i].Cmd := INV_None;
  Sta.Dir.InvSet[i] := false;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_InvAck_1"
  Sta.InvMsg[i].Cmd = INV_InvAck &
  Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true &
  Sta.Dir.Local = true & Sta.Dir.Dirty = false &
  Sta.Dir.HomeInvSet = false & forall j : NODE do j = i | Sta.Dir.InvSet[j] = false end
==>
begin
  Sta.InvMsg[i].Cmd := INV_None;
  Sta.Dir.InvSet[i] := false;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_InvAck_2"
  Sta.InvMsg[i].Cmd = INV_InvAck &
  Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true &
  Sta.Dir.Local = false &
  Sta.Dir.HomeInvSet = false & forall j : NODE do j = i | Sta.Dir.InvSet[j] = false end
==>
begin
  Sta.InvMsg[i].Cmd := INV_None;
  Sta.Dir.InvSet[i] := false;
  Sta.Dir.Pending := false;
endrule;
endruleset;

ruleset i : NODE do
rule "NI_InvAck_3"
  Sta.InvMsg[i].Cmd = INV_InvAck &
  Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true &
  Sta.Dir.Dirty = true &
  Sta.Dir.HomeInvSet = false & forall j : NODE do j = i | Sta.Dir.InvSet[j] = false end
==>
begin
  Sta.InvMsg[i].Cmd := INV_None;
  Sta.Dir.InvSet[i] := false;
  Sta.Dir.Pending := false;
endrule;
endruleset;

rule "NI_Wb"
  Sta.WbMsg.Cmd = WB_Wb
==>
begin
  Sta.WbMsg.Cmd := WB_None;
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := false;
endrule;

rule "NI_FAck"
  Sta.ShWbMsg.Cmd = SHWB_FAck
==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.Dir.Pending := false;
  if (Sta.Dir.Dirty = true) then
    Sta.Dir.HeadPtr := Sta.ShWbMsg.Proc;
    Sta.Dir.HomeHeadPtr := Sta.ShWbMsg.HomeProc;
  end;
endrule;

rule "NI_ShWb"
  Sta.ShWbMsg.Cmd = SHWB_ShWb
==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.Dir.Pending := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.ShrVld := true;
  for p : NODE do
    if (Sta.ShWbMsg.Proc = p & Sta.ShWbMsg.HomeProc = false) | Sta.Dir.ShrSet[p] = true then
      Sta.Dir.ShrSet[p] := true;
      Sta.Dir.InvSet[p] := true;
    else
      Sta.Dir.ShrSet[p] := false;
      Sta.Dir.InvSet[p] := false;
    end;
  end;
  if (Sta.ShWbMsg.HomeProc = true | Sta.Dir.HomeShrSet = true) then
    Sta.Dir.HomeShrSet := true;
    Sta.Dir.HomeInvSet := true;
  else
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
  end;
endrule;

ruleset i : NODE do
rule "NI_Replace"
  Sta.RpMsg[i].Cmd = RP_Replace
==>
begin
  Sta.RpMsg[i].Cmd := RP_None;
  if (Sta.Dir.ShrVld = true) then
    Sta.Dir.ShrSet[i] := false;
    Sta.Dir.InvSet[i] := false;
  end;
endrule;
endruleset;

rule "NI_Replace_Home"
  Sta.HomeRpMsg.Cmd = RP_Replace
==>
begin
  Sta.HomeRpMsg.Cmd := RP_None;
  if (Sta.Dir.ShrVld = true) then
    Sta.Dir.HomeShrSet := false;
    Sta.Dir.HomeInvSet := false;
  end;
endrule;