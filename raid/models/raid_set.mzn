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

% a set based model.
% this takes quite a long time for raid_2.dzn

% the set of warriors
var set of WARRIOR: raid;
constraint card(raid) >= l;
constraint card(raid) <= u;
constraint not (dummy in raid);

% the number of clans that don't like each other
var int: dislike;
constraint dislike = sum(wi, wj in raid where wi < wj)
                        (hates[clan[wi], clan[wj]]);
constraint dislike <= m;

% the objective
var int: obj;
constraint obj = sum(w in raid)(strength[w]);

% solve
solve maximize obj;

% output
output ["raid = \(raid);\nobj = \(obj);"];
