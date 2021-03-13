int: n;


% notes
set of int: NOTE = 1..n;     % domain
set of int: ORDER = 1..n;    % codomain

% another viewpoint: the differences
set of int: NOTE1 = 1..n-1;     % domain
set of int: ORDER1 = 1..n-1;    % codomain

array[ORDER] of var NOTE: order;    % sequence of the notes
array[ORDER1] of var NOTE1: diffs;  % sequence of the differences

array[NOTE] of var ORDER: posn;      % at which position is the note?
array[NOTE1] of var ORDER1: dposn;   % at which position is the difference?

% not alldifferent required; an inverse will enforce the permutation (bijection)
include "inverse.mzn";

constraint inverse(order, posn);
constraint inverse(diffs, dposn);

constraint forall(i in ORDER1)(diffs[i] = abs(order[i+1] - order[i]));
constraint abs(posn[1] - posn[n]) = 1;
%constraint dposn[n-1] = min(posn[1], posn[n]);

solve satisfy;

output ["order = \(order);\n", 
        "diffs = \(diffs);\n", 
        "posn  = \(posn);\n", 
        "dposn = \(dposn);\n"
];

