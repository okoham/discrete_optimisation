int: n;                         % number of court members
set of int: COURT = 1..n;
int: emperor = 1;
array[COURT] of int: rank;
array[COURT] of int: ability;

int: m;                         % number of horses
set of int: HORSE = 1..m;
array[HORSE] of int: beauty;
array[HORSE] of int: speed;

array[COURT,HORSE] of int: enjoy;

/*
Emperor Xian desires a hunt to be organized by Liu Bei to celebrate the emperor’s birthday. To
make the hunt a success, Liu Bei must carefully match the court members to their horses so that
everyone enjoys the day. There may be more court members than horses, in which case some court
members will not ride, but each horse must be used. There may be more horses than court members
in which case each court member must ride. 


In truth the constraints are too hard to satisfy usually. 
So the last constraint can be violated for a penalty of 100 for each violation to the objective.
*/

set of int: COURT0 = 0..n;
set of int: HORSE0 = 0..m;

array[COURT] of var HORSE0: horse;  % which horse is allocated to a court member (can be none = 0)
array[HORSE] of var COURT0: rider;  % which rider is allocated to a horse (can be none = 0)

% include "alldifferent_except_0.mzn";
% constraint alldifferent_except_0(horse);
% constraint alldifferent_except_0(rider);

constraint forall(c in COURT)(horse[c] != 0 -> rider[horse[c]] = c);
constraint forall(h in HORSE)(rider[h] != 0 -> horse[rider[h]] = h);

% The emperor must enjoy the day more than anyone else.
constraint forall(c in COURT where c != emperor /\ horse[c] > 0)
                 (enjoy[emperor, horse[emperor]] > enjoy[c, horse[c]]);
                 
% All court members must ride unless there is no horse left available,
constraint count(c in COURT)(horse[c] != 0) = min(n, m);
constraint count(h in HORSE)(rider[h] != 0) = min(n, m);

% cannot assign a horse with negative enjoy
constraint forall(c in COURT where horse[c] > 0)(enjoy[c, horse[c]] >= 0);

% If a court member holds a higher rank than another, then either 
% (a) the beauty of their horse can be no less than that assigned to the other, 
% (b) the lower rank member does not ride, or
% (c) both court members do not ride.
% constraint forall(c1, c2 in COURT where horse[c1] != 0 /\ horse[c2] != 0)
%                  (rank[c1] > rank[c2] -> beauty[horse[c1]] >= beauty[horse[c2]]);
constraint forall(c1, c2 in COURT where rank[c1] > rank[c2])
                 ((horse[c1]*horse[c2] > 0) -> (beauty[horse[c1]] >= beauty[horse[c2]]) 
                 \/ horse[c2] = 0 
%                  \/ (horse[c1] = 0 /\ horse[c2] = 0)
                 );

% If a horse is faster than another then either 
% (a) the rider of the faster horse has no less riding ability than that of the slower horse, 
% (b) the faster horse has no rider, or 
% (c) both horses have no rider.

% var int: violations = sum(h1, h2 in HORSE where speed[h1] > speed[h2]) 
%                          (
%                          (ability[rider[h1]] < ability[rider[h2]]) 
%                          \/ (rider[h1] = 0 /\ rider[h2] != 0) 
%                          %\/ (rider[h1] != 0 /\ rider[h2] != 0)
%                          ); 


% constraint forall(h1, h2 in HORSE where speed[h1] > speed[h2]) 
%                          (
%                          (ability[rider[h1]] >= ability[rider[h2]]) 
%                          \/ rider[h1] = 0
% %                          \/ (rider[h1] = 0 /\ rider[h2] != 0) 
% %                          \/ (rider[h1] = 0 /\ rider[h2] = 0)
%                          ); 

% The aim is maximize the total enjoyment of the hunt over all riders. 
var int: obj = sum(c in COURT where horse[c] > 0)(enjoy[c, horse[c]]);

%solve satisfy;
solve maximize obj;

output ["horse = \(horse);\n" ++ "rider = \(rider);\n" ++ "obj = \(obj);\n" ];