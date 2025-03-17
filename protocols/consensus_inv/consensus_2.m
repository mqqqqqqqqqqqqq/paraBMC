const
    QUORUMNUMS : 2;
    VALUENUMS : 1;
    NODENUMS : 3;

type
    quorum: scalarset(QUORUMNUMS);
    node: scalarset(NODENUMS);
    value: scalarset(VALUENUMS);

    member_idx : array [quorum] of boolean;
    vote_request_msg_idx : array [node] of boolean;
    vote_msg_idx : array [node] of boolean;
    votes_idx : array [node] of boolean;
    leader_idx : array [quorum] of boolean;
    decided_idx : array [value] of boolean;
    decided_idx_idx : array [quorum] of decided_idx;

var
    member : array [node] of member_idx;
    vote_request_msg : array [node] of vote_request_msg_idx;
    voted : array [node] of boolean;
    vote_msg : array [node] of vote_msg_idx;
    votes : array [node] of votes_idx;
    leader : array [node] of leader_idx;
    voting_quorum : array [quorum] of boolean;
    decided : array [node] of decided_idx_idx;



ruleset q : quorum; v : value do
startstate "Init"
  for m : node do
    for z : node do
      voted[m] := false;
      vote_request_msg[m][z] := false;
      vote_msg[m][z] := false;
      votes[m][z] := false;
      leader[m][q] := false;
      voting_quorum[q] := false;
      decided[m][q][v] := false;
    end;
  end;
endstartstate;
endruleset;



ruleset src : node;dst : node do
rule "send_request_vote"
  true
  --(member[1][1] = true & member[1][2] = true) | (member[2][1] = true & member[2][2] = true) | (member[3][1] = true & member[3][2] = true)
==>
begin
  for m : node do
      for z : node do
      if vote_request_msg[m][z] = true | (m = src & z = dst) then
          vote_request_msg[m][z] := true;
      else
          vote_request_msg[m][z] := false;
      end;
      end;
  end;
for N : node do
  for Q : quorum do
    member[N][Q] := member[N][Q];
  end;
end;

--  for N : node do
--    for Q : quorum do
--      if member[N][Q] = true then
--        member[N][Q] := true;
--      else
--        member[N][Q] := false;
--      end;
--    end;
--  end;
endrule;endruleset;

ruleset src : node;dst : node do
rule "send_vote"

  --(member[1][1] = true & member[1][2] = true) | (member[2][1] = true & member[2][2] = true) | (member[3][1] = true & member[3][2] = true)
 -- &
  voted[src] = false & vote_request_msg[dst][src] = true
==>
begin
  for m : node do
      for z : node do
        if vote_msg[m][z] = true | (m = src & z = dst) then
          vote_msg[m][z] := true;
        else
          vote_msg[m][z] := false;
        end;
      end;
  end;
  for n : node do
    if voted[n] = true | n = src then
      voted[n] := true;
    else
      voted[n] := false;
    end;
  end;
for N : node do
  for Q : quorum do
    member[N][Q] := member[N][Q];
  end;
end;

endrule;endruleset;

ruleset n : node;sender : node do
rule "recv_vote"

  --(member[1][1] = true & member[1][2] = true) | (member[2][1] = true & member[2][2] = true) | (member[3][1] = true & member[3][2] = true)
 -- &
  vote_msg[sender][n] = true
==>
begin
  for m : node do
      for z : node do
        if votes[m][z] = true | (m = n & z = sender) then
          votes[m][z] := true;
        else
          votes[m][z] := false;
        end;
      end;
  end;
for N : node do
  for Q : quorum do
    member[N][Q] := member[N][Q];
  end;
end;

endrule;endruleset;

ruleset q : quorum;sn : node do
rule "choose_voting_quorum"

  --(member[1][1] = true & member[1][2] = true) | (member[2][1] = true & member[2][2] = true) | (member[3][1] = true & member[3][2] = true)
 -- &
  forall n : node do member[n][q] = true -> votes[sn][n] = true end
==>
begin
  for qq : quorum do
    if qq = q then
      voting_quorum[qq] := true;
    else
      voting_quorum[qq] := false;
    end;
  end;
for N : node do
  for Q : quorum do
    member[N][Q] := member[N][Q];
  end;
end;

endrule;endruleset;

ruleset q : quorum;n : node do
rule "become_leader"

  --(member[1][1] = true & member[1][2] = true) | (member[2][1] = true & member[2][2] = true) | (member[3][1] = true & member[3][2] = true)
 -- &
  voting_quorum[q] = true & forall sn : node do (member[sn][q] = true -> votes[n][sn] = true) end
==>
begin
  for nn : node do
    for qq : quorum do
      if leader[nn][qq] = true | (nn = n & qq = q) then 
        leader[nn][qq] := true;
      else
        leader[nn][qq] := false;
      end;
    end;
  end;
for N : node do
  for Q : quorum do
    member[N][Q] := member[N][Q];
  end;
end;

endrule;endruleset;

ruleset n : node;q : quorum;v : value do
rule "decide"

  --(member[1][1] = true & member[1][2] = true) | (member[2][1] = true & member[2][2] = true) | (member[3][1] = true & member[3][2] = true)
 -- &
  leader[n][q] = true & forall sq : quorum do forall sv : value do decided[n][sq][sv] = false end end
==>
begin
  for nn : node do
    for qq : quorum do
      for vv : value do
      if decided[nn][qq][vv] = true | (nn = n & qq = q & vv = v) then
        decided[nn][qq][vv] := true;
      else
        decided[nn][qq][vv] := false;
      end;
      end;
    end;
  end;
for N : node do
  for Q : quorum do
    member[N][Q] := member[N][Q];
  end;
end;

endrule;endruleset;


axiom "axiom1"
forall M : quorum do exists N : node do 
  member[N][M] = true & member[N][M] = true
end end;

invariant "test_1"
  !(member[1][1] = false & member[2][1] = false & member[3][1] = false);



