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

array[1..u] of var NEGOTIATOR: team;

% team in strictly descending order, all different except dummy
constraint forall(i in 1..u-1)
                 (team[i] >= team[i+1] + (team[i] != dummy));
                 
% min cardinality
% we know that dummies are at the end. It's sufficient to check the first l positions.
constraint forall(i in 1..l)(team[i] != dummy);

% strength: sum of strength of negotiator pairs
constraint sum(i, j in 1..u where i < j)(joint[team[i], team[j]]) >= m;

% objective: minimum honor
% how to calculate the minimum of a set while avoiding option types
% and how to deal with the dummy values
int: larger = max(honor) + 1;
var int: obj;
constraint obj = min(i in 1..u)(honor[team[i]] + (team[i] = dummy)*larger);

% objective: maximise honor
solve maximize obj;

% make a proper set from the array; remove the dummy
set of NEGOTIATOR: party :: output_only
                         = { fix(team[i]) | i in 1..u } diff { dummy };

output ["party = \(party);\nobj = \(obj)"];