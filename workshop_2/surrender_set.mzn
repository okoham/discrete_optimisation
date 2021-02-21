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

% strength: sum of strength of negotiator pairs
constraint sum(i, j in party where i < j)(joint[i, j]) >= m;

% objective: minimum honor 
% with this way of modeling it, we get rid of the optionality problem
var int: minhonor;
constraint minhonor = min(i in NEGOTIATOR where i in party)(honor[i]);

solve maximize minhonor;

output ["party = \(party);\nobj = \(minhonor)"];