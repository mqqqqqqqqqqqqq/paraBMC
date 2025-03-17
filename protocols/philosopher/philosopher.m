const 
  NODE_NUM : 2;

type
  philosopher_num : scalarset(NODE_NUM);
  flag_sum : 2..NODE_NUM;
  philosopher_state : enum {thinking, hungry, eating};

var
  fork : array[philosopher_num] of boolean;
  state : array[philosopher_num] of philosopher_state;

ruleset i : philosopher_num do
startstate "Init"
  state[i] := thinking;
  fork[i] := false;
endstartstate;
endruleset;

ruleset i : philosopher_num do
rule "thinking"
  state[i] = thinking
==>
begin
  state[i] := hungry;
endrule;
endruleset;

ruleset i : philosopher_num; flag_num1 : flag_sum do
rule "picking up forks"
  state[i] = hungry &
  fork[i] = false &
  forall j : philosopher_num do
    (i != j & (j = i % flag_num1 + 1)) -> fork[j] = false
    -- (i != j % i & j = i % 1) -> fork[j] = false 
  end
==>
begin
  fork[i] := true;
  for j : philosopher_num do
    if j = ((i % flag_num1) + 1) then
      fork[j] := true;
    end;
  end;
  state[i] := eating;
endrule;
endruleset;

ruleset i : philosopher_num do
rule "eating"
  state[i] = eating
==>
begin
  state[i] := thinking;
  fork[i] := false;
  for j : philosopher_num do
    for flag_num2 : flag_sum do
      if (j = i % flag_num2 + 1) then
        fork[j] := false;
      end;
    end;
  end;
endrule;
endruleset;


