/*
Erster Versuch: läuft, aber nicht richtig. und zu langsam.
*/

int: T; % maximum time allowed;
set of int: TIME = 1..T;
set of int: TIME0 = 0..T; % the states between the steps

int: E; % weight of elephant in STONES;
set of int: STONE = 0..E;

int: G; % number of guards
set of int: GUARD = 1..G;
array[GUARD] of STONE: easy;
array[GUARD] of STONE: hard;
array[GUARD] of TIME: tired;

GUARD: p; % maximum people on pier;
GUARD: b; % maximum people on boat;

set of int: ACT = -1..E; % -1 = goto bank, 0 = wait, > 0 carry stones
int: wait = 0;
int: to_bank = -1;
array[GUARD,TIME] of var ACT: act;        % action at time t
var TIME: end;                            % end time;

%enum POS = {bank, boat};

% where are the guards in each state
array[GUARD,TIME0] of var bool: guard_on_bank;
constraint forall(g in GUARD)(guard_on_bank[g,0]);
% constraint forall(g in GUARD, t in TIME)
%                  (act[g,t] > 0 -> (guard_on_bank[g,t-1]) /\ (not guard_on_bank[g,t]));
% constraint forall(g in GUARD, t in TIME)
%                  (act[g,t] < 0 -> (not guard_on_bank[g,t-1]) /\ (guard_on_bank[g,t]));
% constraint forall(g in GUARD, t in TIME)
%                  (act[g,t] = 0 -> (guard_on_bank[g,t-1] /\ guard_on_bank[g,t]) \/ 
%                                   (not guard_on_bank[g,t-1] /\ not guard_on_bank[g,t]));
constraint forall(g in GUARD, t in TIME)(
                 (guard_on_bank[g,t-1] /\ guard_on_bank[g,t] -> act[g,t] = wait) /\
                 (guard_on_bank[g,t-1] /\ not guard_on_bank[g,t] <-> act[g,t] > 0) /\
                 (not guard_on_bank[g,t-1] /\ not guard_on_bank[g,t] -> act[g,t] = wait) /\
                 (not guard_on_bank[g,t-1] /\ guard_on_bank[g,t] -> act[g,t] = to_bank));

%                                   (not guard_on_bank[g,t-1] /\ act[g,t] < 0 -> guard_on_bank[g,t]) /\
%                  (not guard_on_bank[g,t-1] /\ act[g,t] = 0 -> not guard_on_bank[g,t]));
%                  (not guard_on_bank[g,t-1] /\ guard_on_bank[g,t] -> act[g,t] = 0) /\
% constraint forall(g in GUARD, t in TIME)
%                  (act[g,t] < 0 -> (not guard_on_bank[g,t-1]) /\ (guard_on_bank[g,t]));
% constraint forall(g in GUARD, t in TIME)
%                  (act[g,t] = 0 -> (guard_on_bank[g,t-1] /\ guard_on_bank[g,t]) \/ 
%                                   (not guard_on_bank[g,t-1] /\ not guard_on_bank[g,t]));

% max stones a guard can carry
constraint forall(t in TIME, g in GUARD)(act[g,t] <= hard[g]);

% people on pier during a step
constraint forall(t in TIME)(count(g in GUARD)((act[g,t] != 0)) <= p);

% people on boat after a step
% array[TIME0] of var 0..G: guards_on_boat;
% constraint guards_on_boat[0] = 0;
% constraint forall(t in TIME)
%                  (guards_on_boat[t] = guards_on_boat[t-1] 
%                                     + count(g in GUARD)(act[g,t] > 0)
%                                     - count(g in GUARD)(act[g,t] < 0));
% constraint forall(t in TIME0)(sum(g in GUARD)(guard_on_bank[g,t]) >= G - p);
array[TIME0] of var 0..G: guards_on_boat = 
      array1d(TIME0, [G - sum(g in GUARD)(guard_on_bank[g,t]) | t in TIME0]);
constraint forall(t in TIME0)(guards_on_boat[t] <= p);
 
% stones on boat after a step
array[TIME0] of var STONE: stones_on_boat;
constraint stones_on_boat[0] = 0 /\ forall(t in TIME)(t >= end -> stones_on_boat[t] >= E);
constraint forall(t in TIME) (
                 (stones_on_boat[t] = stones_on_boat[t-1] 
                                    + sum([ trace("g=\(g), t=\(t), \(if act[g,t] > 0 then act[g,t] else 0 endif)\n", if act[g,t] > 0 then act[g,t] else 0 endif) | g in GUARD ])));

% during a step, movement in one direction only
constraint forall(t in TIME)
                 (forall(g in GUARD)(act[g,t] >= 0) \/ 
                  forall(g in GUARD)(act[g,t] <= 0));

% After the end time each guard must only wait.
constraint forall(t in TIME, g in GUARD)(t > end -> act[g,t] = wait);
constraint forall(t in TIME, g in GUARD)
                 (act[g,t] > easy[g] -> forall(tx in t+1..min(T, t+tired[g]))
                                              (act[g,tx] <= 0));

solve minimize end;

output ["act = array2d(GUARD,TIME,[\n"] ++ 
       [show_int(3, act[g,t]) ++ 
        if g=G /\ t=T then "" else "," endif ++ 
        if t=T /\ g<G then "\n" else "" endif | g in GUARD, t in TIME] ++ 
       ["]);\n"] ++
       ["end = \(end);\n"] ++
       % ["guard_on_bank = \(guard_on_bank);\n"] ++
       ["guards_on_boat (<=\(b)) = " ++ show(guards_on_boat) ++ ";\n"] ++
       ["stones_on_boat (\(E)) = " ++ show(stones_on_boat) ++ ";\n"] ++ 
       ["people_on_pier (<=\(p)) = " ++ show([count(g in GUARD)(act[g,t] != 0) | t in TIME]) ++ ";\n"];
       
% TODO: symmetriy braking (it doesn't matter which guard does what - introduce some orderung etc.

% ex1
% act = array2d(GUARD,TIME,[
% 10, 0,  0, 0,0,0,0,0,0,0,
% 5, -1, 10, 0,0,0,0,0,0,0,
% 5, -1, 10, 0,0,0,0,0,0,0,
% 0,  0, 10, 0,0,0,0,0,0,0]);
% end = 3;

% ex2      
act = array2d(GUARD,TIME,[
0,   0, 5, -1, 10,  0, 0,0,0,0,
15, -1, 0,  0,  0, 15, 0,0,0,0]);
end = 6;

