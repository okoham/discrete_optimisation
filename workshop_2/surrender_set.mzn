% workshop 2: Surrender Negotiations
% select a set of trade negotiation party

/*
select a set of negotiators to make up the party. 
The party must be made up of between l and u negotiators.
The negotiators will work in teams of two.

total negoatiation strength (tns): sum of negotiation stregths of all pairs
tns >= m

party_honor (=obj): minimum honor of the negotiators in the party
*/


enum NEGOTIATOR;
NEGOTIATOR: dummy; 

int: l; % minimum party size
int: u; % maximum party size
int: m; % minimum joint ability

array[NEGOTIATOR] of int: honor;
array[NEGOTIATOR,NEGOTIATOR] of int: joint;

var set of NEGOTIATOR: party;
constraint card(party) >= l;
constraint card(party) <= u;
constraint not (dummy in party);

% objective: minimum honor
% how to calculate the minimum of a set while avoiding option types
int: larger = max(honor) + 1;
var int: obj = min(i in NEGOTIATOR)
                  (if i in party then honor[i] else larger endif);

% strength: sum of strength of negotiator pairs
var int: strength = sum(i in NEGOTIATOR, j in NEGOTIATOR where i < j)
                       ((i in party)*(j in party)*joint[i,j]);
constraint strength >= m;

solve maximize obj;

output ["party = \(party);\nobj = \(obj)"];