const 
    NODENUMS : 2;
    DATANUMS: 2;
			
type 
     state : enum{I, T, C, E};

     DATA: scalarset(DATANUMS);
     NODE: scalarset(NODENUMS);

     status : record 
       st:state; 
       data: DATA; 
      end;

var 
    n : array [NODE] of status;

    x : boolean; 
    
    auxDATA : DATA;
    
    memDATA: DATA;



startstate "Init"
for d : DATA do
 for i: NODE do
    n[i].st := I; 
    n[i].data:=d;
  endfor;
  x := true;
  auxDATA := d;
  memDATA:=d;
endfor;
endstartstate;


ruleset i : NODE do
rule "Try" 
      n[i].st = I 
==>
begin
      n[i].st := T;
endrule;endruleset;


ruleset i : NODE do
rule "Crit"
      n[i].st = T & 
      x = true 
==>
begin
      n[i].st := C;
      x := false;
      n[i].data := memDATA; 
endrule;endruleset;


ruleset i : NODE do
rule "Exit"
      n[i].st = C 
==>
begin
      n[i].st := E;
endrule;endruleset;
      
 
ruleset i : NODE do
rule "Idle"
      n[i].st = E 
==>
begin 
      n[i].st := I;
      x := true; 
      memDATA := n[i].data; 
endrule;endruleset;

ruleset i : NODE; d : DATA do rule "Store"
	n[i].st = C
==>
begin
      auxDATA := d;
      n[i].data := d; 
endrule;endruleset;    


invariant "coherence"
  forall i : NODE do
    forall j : NODE do
      i != j -> (n[i].st = C -> n[j].st != C)
end   end;


invariant "c51"
forall i : NODE do
  forall j : NODE do
  (i != j -> 
  (n[i].st= C -> n[i].data =auxDATA) &
  (n[j].st= C -> n[j].data =auxDATA))
end   end;