/*
Zweiter Versuch: funktioniert aus meiner sicht korrekt; könnte schneller sein.
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

enum POS = {bank, boat};
array[GUARD, TIME0] of var POS: guardpos;

% where are the guards in initial state
constraint forall(g in GUARD)(guardpos[g,0] = bank);

% max stones a guard can carry - redundant, ACT ist beschränkt auf max(hard)
constraint forall(t in TIME, g in GUARD)(act[g,t] <= hard[g]);

% people on pier during a step
constraint forall(t in TIME)(count(g in GUARD)((act[g,t] != 0)) <= p);

% people on boat after a step
constraint forall(t in TIME0)(count(g in GUARD)(guardpos[g,t] = boat) <= b);
 
% stones on boat after a step. there may be more than E stones on the boat!                                   
predicate sufficient_stones(TIME: t) = 
    sum(g in GUARD, tx in 1..t)(act[g,tx]*(act[g,tx] > 0)) >= E;
constraint forall(t in TIME)(t >= end -> sufficient_stones(t));
% constraint forall(t in end..T)(
%     let {var 0..max(hard)*G*(T+1) div 2: s = sum(g in GUARD, tx in 1..t)(act[g,tx]*(act[g,tx] > 0)); } in
%     s >= E
% );

% during a step, movement in one direction only
constraint forall(t in TIME)
                 (forall(g in GUARD)(act[g,t] >= 0) \/ 
                  forall(g in GUARD)(act[g,t] <= 0));
                  
% behaviour of guards
predicate guard(var POS: pos, var POS: nextpos, var ACT: action, var bool: fit) = 
    (pos = bank /\ nextpos = boat /\ action > 0 /\ fit) \/
    (pos = boat /\ nextpos = bank /\ action = to_bank) \/
    (pos = nextpos /\ action = wait);
    
% guard is fit if he did not carry any heavy load in steps t-tired .. t-1
% TODO: geht vielleich auch einfacher, ohne if?
predicate guard_is_fit(GUARD: g, TIME: t) = 
    let { var TIME: tmin = if t>tired[g] then t-tired[g] else 1 endif; } in 
    forall(tx in tmin..t-1)(act[g,tx] <= easy[g]);
 
constraint forall(g in GUARD, t in TIME)
                 (guard(guardpos[g,t-1], guardpos[g,t], act[g,t], guard_is_fit(g,t))); 

% After the end time each guard must only wait.
constraint forall(t in TIME, g in GUARD)(t > end -> act[g,t] = wait);

% guards can carry up to hard stones.
constraint forall(t in TIME, g in GUARD)(act[g,t] <= hard[g]);

solve minimize end;

output ["act = array2d(GUARD,TIME,[\n"] ++ 
       [show_int(3, act[g,t]) ++ 
        if g=G /\ t=T then "" else "," endif ++ 
        if t=T /\ g<G then "\n" else "" endif | g in GUARD, t in TIME] ++ 
       ["]);\n"] ++
       ["end = \(end);\n"] ++
       % ["guard_on_bank = \(guard_on_bank);\n"] ++
       %["guards_on_boat (<=\(b)) = " ++ show([sum([guardpos[g,t] = boat | g in GUARD]) | t in TIME0]) ++ ";\n"] ++
       %["stones_on_boat (\(E)) = " ++ show(stones_on_boat) ++ ";\n"] ++ 
       %["people_on_pier (<=\(p)) = " ++ show([count(g in GUARD)(act[g,t] != 0) | t in TIME]) ++ ";\n"] ++ 
       %["maxstones = \(maxstones);\n"] ++
       [""];
       
% TODO: symmetriy braking (it doesn't matter which guard does what - introduce some orderung etc.
