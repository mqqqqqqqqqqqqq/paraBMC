const
  NODENUMS : 4;
  VALUENUMS : 2;
  QUORUMNUMS : 2;
  ROUNDNUMS : 2;

type
  node : scalarset(NODENUMS);
  value : scalarset(VALUENUMS);
  quorum : scalarset(QUORUMNUMS);
  round : scalarset(ROUNDNUMS);
  one_b_max_vote_idx : array[round] of array[value] of boolean;
  vote_idx : array[value] of boolean;
  decision_idx : array[value] of boolean;

var
  le: array[round] of array[round] of boolean;
  member: array[node] of array[quorum] of boolean;
  one_a: array[round] of boolean;
  one_b_max_vote: array[node] of array[round] of one_b_max_vote_idx;
  one_b: array[node] of array[round] of boolean;
  left_rnd: array[node] of array[round] of boolean;
  proposal: array[round] of array[value] of boolean;
  vote: array[node] of array[round] of vote_idx;
  decision: array[node] of array[round] of decision_idx;



ruleset P: round ; Q: round ; N: node; V: value do
startstate "Init"
  one_a[P] := false;
  one_b[N][P] := false;
  left_rnd[N][P] := false;
  proposal[P][V] := false;
  vote[N][P][V] := false;
  decision[N][P][V] := false;
  one_b_max_vote[N][P][Q][V] := false;
endstartstate;
endruleset;


ruleset r: round; none: round do
rule "send_a"
  --r != none
  r != none
==>
begin
  one_a[r] := true;
endrule;endruleset;

ruleset n: node; r: round; maxr:round; v:value; none: round do
rule "join_round_case1"
  r != none & one_a[r] = true & left_rnd[n][r] = false & 
  maxr = none & forall MAXR: round do forall V: round do
  !(le[r][MAXR]=false & vote[n][MAXR][V] = true) end end
==>
begin
  one_b_max_vote[n][r][maxr][v] := true;
  one_b[n][r] := true;
  for R:round do
    if (left_rnd[n][R]=true | le[r][R]=false) then
      left_rnd[n][R] := true;
    else
      left_rnd[n][R] := false;
    end;
  end;
endrule;endruleset;


ruleset n: node; r: round; maxr:round; v:value; none: round do
rule "join_round_case2"
  r != none & one_a[r] = true & left_rnd[n][r] = false & 
  maxr != none & le[r][maxr] = false & vote[n][maxr][v]=true & 
  forall MAXR: round do forall V: round do
  (le[r][MAXR]=false & vote[n][MAXR][V] = true) -> le[MAXR][maxr]=true end end
==>
begin
  one_b_max_vote[n][r][maxr][v] := true;
  one_b[n][r] := true;
  for R:round do
    if (left_rnd[n][R]=true | le[r][R]=false) then
      left_rnd[n][R] := true;
    else
      left_rnd[n][R] := false;
    end;
  end;
endrule;endruleset;


ruleset  r: round; q:quorum; maxr:round; v:value; none: round do
rule "propose_case1"
  r != none & forall V:value do proposal[r][V]=false end & 
  forall N:node do member[N][q]=true -> one_b[N][r]=true end & 
  maxr = none & forall N:node do forall MAXR:round do forall V:value do 
  !(member[N][q]=true & le[r][MAXR] = false & vote[N][MAXR][V]=true) end end end
==>
begin
  proposal[r][v] := true;
endrule;endruleset;


ruleset  r: round; q:quorum; maxr:round; v:value; none: round do
rule "propose_case2"
  r != none & forall V:value do proposal[r][V]=false end & 
  forall N:node do member[N][q]=true -> one_b[N][r]=true end & 
  maxr != none & !forall N:node do !(member[N][q]=true & le[r][maxr]=false & vote[N][maxr][v]=true) end & 
  forall N:node do forall MAXR:round do forall V:value do 
  (member[N][q]=true & le[r][MAXR] = false & vote[N][MAXR][V]=true) -> le[MAXR][maxr]=true end end end
==>
begin
  proposal[r][v] := true;
endrule;endruleset;


ruleset  n: node; v:value; r:round; none: round do
rule "cast_vote"
  r != none & left_rnd[n][r]=false & proposal[r][v]=true
==>
begin
  vote[n][r][v] := true;
endrule;endruleset;


ruleset  n: node; v:value; r:round; q:quorum; none: round do
rule "decide"
  r != none & forall N:node do member[N][q]=true -> vote[N][r][v]=true end
==>
begin
  decision[n][r][v] := true;
endrule;endruleset;

axiom "members"
forall X : quorum do forall Y : quorum do exists N : node do 
  member[N][X] = true & member[N][Y] = true
end end end;


axiom "total_order_1"
forall X: round do
  le[X][X] = true
end;


axiom "total_order_2"
forall X: round do forall Y: round do forall Z: round do
  le[X][Y] = true & le[Y][Z] = true -> le[X][Z] = true
end end end;


axiom "total_order_3"
forall X: round do forall Y: round do
  le[X][Y] = true & le[Y][X] = true -> X = Y
end end;


axiom "total_order_4"
forall X: round do forall Y: round do
  le[X][Y] = true | le[Y][X] = true
end end;