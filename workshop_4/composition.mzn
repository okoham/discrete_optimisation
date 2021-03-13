% chuffed: 2s for n=99
% gecode: 2s for n=99
% coin-bc: 8s for n=10

int: n;
%n = 8;

% notes
set of int: NOTE = 1..n;     % domain
set of int: ORDER = 1..n;    % codomain

% another viewpoint: the differences
set of int: NOTE1 = 1..n-1;     % domain
set of int: ORDER1 = 1..n-1;    % codomain

array[ORDER] of var NOTE: order;  % order (sequence) of the notes
array[ORDER1] of var NOTE1: diffs;  % order of the differences


include "alldifferent.mzn";
constraint alldifferent(order);
constraint alldifferent(diffs);

constraint forall(i in ORDER1)(diffs[i] = abs(order[i+1] - order[i]));

solve satisfy;

% output
%int: digits = if n <= 9 then 1 else 2 endif;
int: digits = ceil(ln(n+1) / ln(10));   % alternative way
string: sep = concat([ " " | i in 1..digits ]);
% hint: could also use show_int
output [join(sep, [format(digits, x) | x in order]), "\n", 
        sep, join(sep, [format(digits, x) | x in diffs])];