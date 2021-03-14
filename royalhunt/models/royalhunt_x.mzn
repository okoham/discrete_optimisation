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

% channeling
constraint forall(c in COURT, h in HORSE)(horse[c] = h <-> rider[h] = c); 


array[COURT] of var HORSE0: horse;  % which horse is allocated to a court member (can be none = 0)
array[HORSE] of var COURT0: rider;  % which rider is allocated to a horse (can be none = 0)

% total enjoyment
% cannot assign a horse with negative enjoy
array[COURT] of var 0..max(enjoy): enjoyment = [enjoy[c, horse[c]] | c in COURT];


% The emperor must enjoy the day more than anyone else.
constraint forall(c in 2..n)
                 (enjoy[emperor, horse[emperor]] > enjoy[c, horse[c]]);
                 

% If a court member holds a higher rank than another, then either 
% (a) the beauty of their horse can be no less than that assigned to the other, 
% (b) the lower rank member does not ride, or
% (c) both court members do not ride.
constraint forall(c1, c2 in COURT where rank[c1] > rank[c2])
                 (beauty[horse[c1]] >= beauty[horse[c2]]);

% If a horse is faster than another then either 
% (a) the rider of the faster horse has no less riding ability than that of the slower horse, 
% (b) the faster horse has no rider, or 
% (c) both horses have no rider.
% max m-1 violations
% var 0..m-1: violations = sum(h1, h2 in HORSE where h1 != h2)
%             ((speedx[h1] > speedx[h2]) /\ (abilityx[rider[h1]] < abilityx[rider[h2]]));

% The aim is maximize the total enjoyment of the hunt over all riders. 
var int: obj = sum(enjoyment); % - 100*violations;

% solve satisfy;
solve maximize obj;

output ["horse = \([if horse[c] <= m then horse[c] else 0 endif | c in COURT]);\n" 
        %++ "rider = \(rider);\n" 
        ++ "rankx =   \(rank);\n"
        ++ "speedx =  \(speed);\n"
        ++ "beautyx = \(beauty);\n"
        ++ "enjoyment = \(enjoyment);\n"
%         %++ "enjoyx = " ++ show(enjoyx) ++ ";\n"
%         ++ show(max(enjoy))
        ++ "obj = \(obj);\n" 
        ];