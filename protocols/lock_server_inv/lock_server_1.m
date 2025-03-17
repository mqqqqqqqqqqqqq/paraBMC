const
    SERNUMS : 1;
    CLINUMS : 2;

type
    client: scalarset(CLINUMS);
    server: scalarset(SERNUMS);
    link_idx : array [server] of boolean;

var
    link : array [client] of link_idx;
    semaphore : array [server] of boolean;

startstate "Init"
for i: client do
  for h : server do
    semaphore[h] := true;
    link[i][h] := false;
  endfor;
endfor;
endstartstate;

ruleset x : client; y : server do
rule "connect"
  semaphore[y] = true
==>
begin
  link[x][y] := true;
  semaphore[y] := false;
endrule;endruleset;

ruleset x : client; y : server do
rule "disconnect"
  link[x][y] = true
==>
begin
  link[x][y] := false;
  semaphore[y] := true;
endrule;endruleset;

invariant "test_1"
    !(link[1][1] = true & semaphore[1] = true);
