% 1.3 Simple Decision - x110.mzn
% Build a MiniZinc model x110.mzn with a single decision variable x taking values from one to ten,
% which outputs it value.
% Test that it prints out all solutions. In the IDE you can do this by in the Configuration tab,
% changing from “Default behavior” to “User-defined behavior” and change the number in “Stop
% after this many solutions (0 means ”all”)” to 0. You can test it on the command line using
% minizinc x110.mzn -a

var 1..10: x;
output ["\(x)\n"];