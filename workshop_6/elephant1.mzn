% TODO: schneller machen !!!

int: T; % maximum time allowed;
set of int: TIME = 1..T;
int: G; % number of guards
int: F; 
int: W;

array[TIME] of var -F..F: move_food;      % move food +ve bank to boat, -ve boat to bank
array[TIME] of var -W..W: move_water;     % move water +ve bank to boat, -ve boat to bank
var TIME: end;                            % end time;

% Cao Chong has G guards, W bowls of water and F bowls of food together with the elephant
% on the bank.

% TIME describes the intervals in which something is moved.
% TIME0 are the states after the movement; 0 is initial state
set of int: TIME0 = 0..T;

% where is the stuff and elephant at any time?
enum POSITION = {bank, boat};
array[POSITION] of POSITION: opposite = [boat, bank];

% position of elephant, initial condition
array[TIME0] of var POSITION: elephant; 
constraint elephant[0] = bank;

% position of stuff, initial condition
array[TIME0, POSITION] of var 0..F: food;
array[TIME0, POSITION] of var 0..W: water;
constraint food[0, bank] = F;
constraint water[0, bank] = W;

% stuff at any time is constant
constraint forall(t in TIME0)(sum(p in POSITION)(food[t, p]) = F);
constraint forall(t in TIME0)(sum(p in POSITION)(water[t, p]) = W);

% include "global_cardinality.mzn";
% constraint global_cardinality([food[t, bank] + food[t, boat] | t in TIME0 ], [F], [T+1]);
% constraint global_cardinality([water[t, bank] + water[t, boat] | t in TIME0 ], [F], [T+1]);

% amount of food/water at t+1 = amount at t plus moved stuff
% +ve ... bank to boat; -ve ... boat to bank
% need to consider boat only; bank is handled by sum constraints above
constraint forall(t in TIME)(food[t, boat] = food[t-1, boat] + move_food[t]);
constraint forall(t in TIME)(water[t, boat] = water[t-1, boat] + move_water[t]);


% The elephant will move to the boat if 
% (a) there is an equal number of bowls of food and water on the boat, 
% (b) the boat has more bowls of food than those on the bank and 
% (c) the boat has more bowls of water than those on the bank. 
    
% Unfortunately the elephant will move back to the bank if 
% (1) the elephant is on the boat, 
% (2) there is an equal number of bowls of food and water on the bank, 
% (3) the bank has more bowls of food than those on the boat and 
% (4) the bank has more bowls of water than those on the boat.
  
predicate elephant_moves(TIME0: t) =  
    let {
        var POSITION: current = elephant[t]; 
        var POSITION: other = opposite[current];
    } in
    food[t,other] = water[t,other] /\ 
    food[t,other] > food[t,current] /\ 
    water[t,other] > water[t,current]; 
  
% what does the elephant do? 
constraint forall(t in TIME, p in POSITION)
                 ((elephant[t-1] = p /\ elephant_moves(t-1)) -> elephant[t] = opposite[p]);
constraint forall(t in TIME, p in POSITION)
                 ((elephant[t-1] = p /\ not elephant_moves(t-1)) -> elephant[t] = p);

  
% The elephant will eat if there is only food left where it is and it (the food) doesn’t move.
% Similarly the elephant will drink if there is only water left where it is and it doesn’t move. 

% If the elephant either eats or drinks then the weighing will be wrong since it will include 
% the weight of the food or drink. Hence eating and drinking can’t be allowed.
 
predicate no_eat_or_drink(TIME: t) = 
   let {
       var POSITION: current = elephant[t];
       % away = 1 if food is moved away from the elephant's current position
       var bool: away = (current = bank /\ max(move_food[t], move_water[t]) > 0) \/ 
                        (current = boat /\ min(move_food[t], move_water[t]) < 0);
       var 0..F: available_food = food[t-1, current] - away*abs(move_food[t]); 
       var 0..W: available_water = water[t-1, current] - away*abs(move_water[t]); 
   } in
   (available_water > 0 \/ available_food = 0) /\
   (available_water = 0 \/ available_food > 0);
   
constraint forall(t in TIME)(no_eat_or_drink(t)); 

% Each guard can carry one bowl of food or water in each step: from bank to boat, or boat to
% bank. 
constraint forall(t in TIME)(abs(move_food[t]) + abs(move_water[t]) <= G);

% All the movements in the same step have to be in the same direction, 
% either from bank to boat, or boat to bank.
constraint forall(t in TIME)(move_food[t] * move_water[t] >= 0);

% The aim is to get the elephant onto the boat, with no food or water left in the boat in the least
% number of steps, and no more than a given T time steps. 
constraint elephant[end] = boat;
constraint water[end, boat] = 0;
constraint food[end, boat] = 0;

% Note that no water or food should be moved after the end step (when the elephant’s weight is
% marked on the boat).
constraint forall(t in end+1..T)(move_food[t] = 0);
constraint forall(t in end+1..T)(move_water[t] = 0);

% solve
solve minimize end;

% FIXME: the output item makes the solver slow ?!?!?!?
% output
%output ["move_food = \(move_food);\nmove_water = \(move_water);\nend = \(end);\n"];