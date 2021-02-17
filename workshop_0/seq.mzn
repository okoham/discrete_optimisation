% 1.6 A Sequence - seq.mzn

% Define a MiniZinc model seq.mzn which takes a integer parameter n defining the length of an array
% of numbers x taking values from 0 to 3. Constrain the numbers so that the first number is zero,
% the last number is 3, and the sum of any two adjacent numbers in the array x is at most 3. Also
% constrain the value of x at positions divisible by 3 to be greater than or equal to 2. Maximize the
% sum of the numbers in the array x. The output should be of the form sum = array of values, e.g.
% 6 = [0,1,2,0,3] given a solution x = [0, 1, 2, 0, 3] for n = 5.

% Test your model for various values d of n using either the IDE pop up box to enter the value
% for n, or from the command line using

% minizinc seq.mzn -D" n = d;"

% Test out at least the values of d from 3 to 9.

int: n;
set of int: INDEX = 1..n;
array[INDEX] of var 0..3: x;

constraint x[1] = 0;
constraint x[n] = 3;
constraint forall(i in 1..n-1)
                 (x[i] + x[i+1] <= 3);
% this is fine, too
% constraint forall(i in 2..n-1 where i mod 3 = 0) 
constraint forall(i in INDEX where i mod 3 = 0)
                 (x[i] >= 2);

solve maximize sum(x);

output [show(sum(x)) ++ " = " ++ show(x) ++ "\n"];