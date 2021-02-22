% assignment 2
% select a set of raiding warrior
enum WARRIOR;
WARRIOR: dummy;
enum CLAN; % the clan they belong too

int: l; % minimum raid party size
int: u; % maximum raid party size
int: m; % limit of hatreds

array[WARRIOR] of int: strength;
array[WARRIOR] of CLAN: clan;

array[CLAN,CLAN] of 0..1: hates;

% an array based model.

% the set of warriors
array[1..u] of var WARRIOR: raidx;
% ordered
constraint forall(w in 1..u-1)
                 (raidx[w] >= (raidx[w] != dummy) + raidx[w+1]);
% lower bound on cardinality
constraint forall(w in 1..l)(raidx[w] != dummy);

% the number of clans that don't like each other
constraint sum(wi, wj in raidx where wi < wj)
              (hates[clan[wi], clan[wj]]) <= m;

% the objective
var int: obj;
constraint obj = sum(w in raidx)(strength[w]);

% solve
solve maximize obj;

% output
% make a proper set from the array; remove the dummy
set of WARRIOR: raid :: output_only
                     = { fix(raidx[w]) | w in 1..u } diff { dummy };
                     
output ["raid = \(raid);\nobj = \(obj);"];
