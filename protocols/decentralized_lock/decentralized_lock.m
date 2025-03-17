const
    NODENUMS : 4;

type
    NODE: scalarset(NODENUMS);
    message_idx : array [NODE] of boolean;

var
    message : array [NODE] of message_idx;
    has_lock : array [NODE] of boolean;

    start_node : NODE;

ruleset i : NODE do
startstate "Init"
  for h : NODE do 
    start_node := i;
    message[i][h] := false;
    has_lock[h] := (h = start_node);
  endfor;
endstartstate;
endruleset;

ruleset src : NODE; dst : NODE do
rule "send"
  has_lock[src] = true
==>
begin
  message[src][dst] := true;
  has_lock[src] := false;
endrule;endruleset;

ruleset src : NODE; dst : NODE do
rule "recv"
  message[src][dst] = true
==>
begin
  message[src][dst] := false;
  has_lock[dst] := true;
endrule;endruleset;

