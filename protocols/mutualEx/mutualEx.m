const
    NODENUMS : 1;

type
     state : enum{I, T, C, E};
     NODE: scalarset(NODENUMS);

var
    n : array [NODE] of state;

    x : boolean;


startstate "Init"
begin
for i : NODE do
  n[i] := I;
  x := true;
end;
endstartstate;


ruleset i : NODE
do rule "Try"
  n[i] = I
==>
begin
  n[i] := T;
endrule;endruleset;


ruleset i : NODE
do rule "Crit"
  n[i] = T & x = true
==>
begin
  n[i] := C;
  x := false;
endrule;endruleset;

ruleset i : NODE
do rule "Exit"
  n[i] = C
==>
begin
  n[i] := E;
endrule;endruleset;

ruleset i : NODE
do rule "Idle"
  n[i] = E
==>
begin
  n[i] := I;
  x := true;
endrule;endruleset;


