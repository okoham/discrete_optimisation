% Beauty Trap
% Perform the most seductive dance

enum LEGS = {spin, leap, waltz, curtsey, prep, stand};
enum ARMS = {beckon, out, up, wrapped, neutral};
enum FACE = {smile, wink, batt, think, glow, blank};

int: maxlen;
set of int: STEP = 1..maxlen;
array[LEGS] of int: maxlegs;
array[ARMS] of int: maxarms;
array[FACE] of int: maxface;
constraint assert(maxlegs[stand] >= maxlen, "maxlegs[stand] smaller than maxlen");
constraint assert(maxarms[neutral] >= maxlen, "maxarms[neutral] smaller than maxlen");
constraint assert(maxface[blank] >= maxlen, "maxface[blank] smaller than maxlen");
array[LEGS,ARMS] of int: dance_value;
array[ARMS,FACE] of int: entice_value;
constraint assert(dance_value[stand,neutral] = 0, "incorrect dance_value array");
constraint assert(entice_value[neutral,blank] = 0, "incorrect entice_value array");
int: boredom; % how bored each step make the viewer

var STEP: len;
array[STEP] of var LEGS: legs;
array[STEP] of var ARMS: arms;
array[STEP] of var FACE: face;

% upper limits on how many times she can use the same move
include "global_cardinality_low_up_closed.mzn";
constraint global_cardinality_low_up_closed(legs, LEGS, [0 | i in LEGS], maxlegs);
constraint global_cardinality_low_up_closed(arms, ARMS, [0 | i in ARMS], maxarms);
constraint global_cardinality_low_up_closed(face, FACE, [0 | i in FACE], maxface);

% She must prep before any leap. Directly after a spin she can only curtsey, prep or stand.
% Directly after a leap she can only spin, waltz, or stand. She can waltz at most three times in a row.
% She cannot prep directly after a curtsey. Finally, in between any waltz and a following curtsey there
% must be a stand
constraint forall(i in 2..maxlen)(legs[i] = leap -> legs[i-1] = prep);
constraint forall(i in 1..maxlen-1)(legs[i] = spin -> legs[i+1] in {curtsey, prep, stand});
constraint forall(i in 1..maxlen-1)(legs[i] = leap -> legs[i+1] in {spin, waltz, stand});
constraint forall(i in 1..maxlen-3)(sum(j in 0..3)(legs[i+j] = waltz) <= 3);
constraint forall(i in 1..maxlen-1)(legs[i] = curtsey -> legs[i+1] != prep);
constraint forall(i in 1..maxlen-1)(legs[i] = waltz -> legs[i+1] != curtsey);
constraint forall(i in 1..maxlen-2, j in i+2..maxlen)((legs[i] = waltz /\ legs[j] = curtsey) -> exists(k in i+1..j-1)(legs[k] = stand));
% TODO: stand btwn waltz and curtsey

% She can beckon only directly after out or up (and hence not as the first move).
% She can wrapped only directly after beckon or neutral, including the possibility that wrapped is the
% first move (since the previous move can be considered neutral). She cannot do any of the two same
% moves in a row except neutral.
constraint arms[1] != beckon;
constraint forall(i in 2..maxlen)(arms[i] = beckon -> arms[i-1] in {out, up});
constraint forall(i in 2..maxlen)(arms[i] = wrapped -> arms[i-1] in {beckon, neutral});
constraint forall(i in 1..maxlen-1)(arms[i+1] != arms[i] \/ arms[i+1] = neutral);

% She cannot make more than two of the same gestures in a row except blank. She
% cannot think directly after smile (ing) or batt (ing) her eyelids.
constraint forall(i in 1..maxlen-1)(face[i+1] != face[i] \/ face[i+1] = blank);
constraint forall(i in 1..maxlen-1)(face[i] in {smile, batt} -> face[i+1] != think);

% The combination of her legs move and arms move at each step determines the value of her dance.
int: vmax = max(dance_value);
array[STEP] of var 0..vmax: value = [dance_value[legs[i], arms[i]] | i in STEP];

% The combination of her arms move and facial gesture at each step determines the enticement that
% she achieves.
int: emax = max(entice_value);
array[STEP] of var 0..emax: enticement = [entice_value[arms[i], face[i]] | i in STEP];

% Some combinations of legs move and arms moves are impossible. Similarly some combinations
% of arms move and face would be very off putting and hence must be avoided.
%constraint forall(s in STEP)(dance_value[legs[s], arms[s]] >= 0);
%constraint forall(s in STEP)(entice_value[arms[s], face[s]] >= 0);

% After the dance ends she must stay in the base position stand, neutral, and blank.
%constraint len < maxlen;
constraint forall(i in len+1..maxlen)(legs[i] = stand);
constraint forall(i in len+1..maxlen)(arms[i] = neutral);
constraint forall(i in len+1..maxlen)(face[i] = blank);

% Her aim is to maximize the seductive power of the dance, which is given by the value of the
% dance, plus the enticements of the dance minus the boredom level of Lu Bu multiplied by the length
% of the dance.
var int: obj = sum(value) + sum(enticement) - boredom*len;
solve maximize obj;

% output
output ["len = \(len);\nlegs = \(legs);\narms = \(arms);\nface = \(face);\nobj = \(obj);\n"];


