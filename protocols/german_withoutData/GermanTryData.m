	
const


  NODE_NUM : 2;
  DATA_NUM : 2;

type

  NODE : scalarset(NODE_NUM);
  DATA : scalarset(DATA_NUM);

  OTHER : enum {Other};

  ABS_NODE : union {NODE, OTHER};

  CACHE_STATE : enum{I,S,E};
  CACHE : record
    State : CACHE_STATE;
    Data : DATA;
  end;

  MSG_CMD : enum{Empty,ReqS,ReqE,Inv,InvAck,GntS,GntE};
var

  Cache : array [NODE] of CACHE;
  InvSet : array [NODE] of boolean;
  ShrSet : array [NODE] of boolean;
  E : boolean;
  CurCmd : MSG_CMD;
  CurPtr : ABS_NODE;
  MemData : DATA;
  AuxData : DATA;

startstate "Init"
  E := false;
endstartstate;


