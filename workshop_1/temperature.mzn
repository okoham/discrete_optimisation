% data4.dzn is unsatisfiable

% the outside temperature
array[int] of int: readings;
% inside temperature
int: start; 
int: n = length(readings);
set of int: HOUR = 1..n;
set of int: HOUR0 = 0..n;

enum CHOICE = {heat, strongly_heat, cool, strongly_cool, do_nothing};

array[CHOICE] of int: action_cost = [1, 5, 3, 9, 0];
array[CHOICE] of int: dtemp = [1, 4, -2, -5, 0];

array[HOUR] of var CHOICE: choice;
array[HOUR0] of var 25..30: temp;

constraint temp[0] = start;

%array[HOUR0] of var int: temp;
%constraint forall(h in HOUR)(temp[h] >= 25 /\ temp[h] <= 30);
%constraint forall(h in HOUR)(temp[h] <= 30);
   
constraint forall(h in HOUR)
                 (temp[h] = (temp[h-1] + readings[h]) div 2 + dtemp[choice[h]]);
                        
var int: obj = sum(i in HOUR)(action_cost[choice[i]]);

solve minimize obj;

output ["temp = \(temp)\nchoice = \(choice)\ncost = \(obj)"];
