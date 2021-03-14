% this is the model that was graded. all solutions were correct; except _6 with took too
% long to run

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

int: p = max(n, m);  
set of int: COURTx = 1..p;
set of int: HORSEx = 1..p;

% extended data

% rank of dummy court is less than that of the lowest rank court member
int: dummyrank = min(rank) - 1;
array[COURTx] of int: rankx = rank ++ [ dummyrank | i in n+1..p ];
% ability of dummy court: 
int: dummyability = max(ability) + 1;
array[COURTx] of int: abilityx = ability ++ [ dummyability | i in n+1..p ];
% beauty of dummy horse
int: dummybeauty = min(beauty) - 1;
array[HORSEx] of int: beautyx = beauty ++ [ -1 | i in m+1..p ];
% speed of dummy horse
int: dummyspeed = min(speed) - 1;
array[HORSEx] of int: speedx = speed ++ [ -1 | i in m+1..p ];

% enjoyment of dummy combinations should be zero
int: dummyenjoy = 0;
array[COURTx,HORSEx] of int: enjoyx = array2d(	COURTx, HORSEx, 
                                              [if c <= n /\ h <= m 
                                               then enjoy[c,h] 
                                               else dummyenjoy endif 
                                              | c in COURTx, h in HORSEx ]);

array[COURTx] of var HORSEx: horse;  % which horse is allocated to a court member (can be none = 0)
array[HORSEx] of var COURTx: rider;  % which rider is allocated to a horse (can be none = 0)

include "inverse.mzn";
constraint inverse(horse, rider);

% total enjoyment: cannot assign a horse with negative enjoy
array[COURTx] of var 0..max(enjoy): enjoyment = [enjoyx[c, horse[c]] | c in COURTx];

% The emperor must enjoy the day more than anyone else.
constraint enjoyment[emperor] > max([enjoyment[c] | c in 2..n]);
                 
% If a court member holds a higher rank than another, then either 
% (a) the beauty of their horse can be no less than that assigned to the other, 
% (b) the lower rank member does not ride, or
% (c) both court members do not ride.
constraint forall(c1, c2 in COURT where rankx[c1] > rankx[c2])
                 (beautyx[horse[c1]] >= beautyx[horse[c2]]);

% If a horse is faster than another then either 
% (a) the rider of the faster horse has no less riding ability than that of the slower horse, 
% (b) the faster horse has no rider, or 
% (c) both horses have no rider.
% max p^2 violations
var 0..m^2: violations = sum(h1, h2 in HORSE where speedx[h1] > speedx[h2])
                            (abilityx[rider[h1]] < abilityx[rider[h2]]);

% The aim is maximize the total enjoyment of the hunt over all riders. 
var int: obj = sum(enjoyment) - 100*violations;

% solve satisfy;
solve maximize obj;

output ["horse = \([if horse[c] <= m then horse[c] else 0 endif | c in COURT]);\n" 
        ++ "obj = \(obj);\n" 
%         ++ "horse = \(horse);\n"
%         ++ "rider = \(rider);\n" 
%         ++ "rankx =   \(rankx);\n"
%         ++ "speedx =  \(speedx);\n"
%         ++ "beautyx = \(beautyx);\n"
%         ++ "ability(rider[h]) = \([abilityx[rider[h]] | h in HORSEx ]);\n"
%         ++ "beauty(h[c]) = \([beautyx[horse[c]] | c in COURTx]);\n"
%         ++ "speedx(h) =  \(speedx);\n"
%         ++ "beautyx(h) = \(beautyx);\n"
%         ++ "enjoyment = \(enjoyment);\n"
%         ++ "enjoyx = " ++ show(enjoyx) ++ ";\n"
%         ++ show(max(enjoy))
        ];