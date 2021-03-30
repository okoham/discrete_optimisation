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
set of int: POSITION = 1..2;  
int: bank = 1;
int: boat = 2;
array[POSITION] of POSITION: opposite = [boat, bank];

% position of elephant, initial condition
array[TIME0] of var POSITION: elephant; 
constraint elephant[0] = bank;

% position of stuff, initial condition
array[TIME0, POSITION] of var 0..F: food;
array[TIME0, POSITION] of var 0..W: water;
constraint food[0, bank] = F;
constraint food[0, boat] = 0;
constraint water[0, bank] = W;
constraint water[0, boat] = 0;

% in which direction does stuff move (from, to)?
% set of int: MOVE = -1..1;
% array[POSITION, POSITION] of MOVE: direction = [| 0, 1 | -1, 0 |];
% % int: to_boat = 1;
% % int: to_bank = -1;
% array[POSITION] of int: away = [-1, 1];
% array[POSITION] of int: towards = [1, -1];

% what does the elephant do? 
constraint forall(t in TIME, p in POSITION)
                 ((elephant[t-1] = p /\ elephant_moves(t-1)) -> elephant[t] = opposite[p]);
constraint forall(t in TIME, p in POSITION)
                 ((elephant[t-1] = p /\ not elephant_moves(t-1)) -> elephant[t] = p);


% how much stuff is where at any time?
constraint forall(t in TIME0)(sum(s in POSITION)(food[t, s]) = F);
constraint forall(t in TIME0)(sum(s in POSITION)(water[t, s]) = W);

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
    elephant[t] = current /\ 
    food[t,other] = water[t,other] /\ 
    food[t,other] > food[t,current] /\ 
    water[t,other] > water[t,current]; 
    

% The elephant will eat if there is only food left where it is and it (the food?) doesn’t move.
% wenn food weggebracht wird: food(t) - |move_food(t)| > 0 !!!
% wenn food hingebracht word: food(t) > 0

% Similarly the elephant will drink if there is only water left where it is and it doesn’t move. 

predicate consumes(TIME: t) = 
   let {
       var POSITION: current = elephant[t];
       var POSITION: before = elephant[t-1];
       % away describes if food is moved away from the elephant's current position
       var 0..1: away = if current = bank then
                            if (move_food[t] > 0) \/ (move_water[t] > 0) then 1 else 0 endif
                        else 
                            if (move_food[t] < 0) \/ (move_water[t] < 0) then 1 else 0 endif
                        endif;
       var int: available_food = food[t-1, current] - away*abs(move_food[t]); 
       var int: available_water = water[t-1, current] - away*abs(move_water[t]); 
   } in
   (available_water > 0 /\ available_food = 0) \/
   (available_water = 0 /\ available_food > 0);
   

% If the elephant either eats or drinks then the weighing will be wrong since it will include 
% the weight of the food or drink. Hence eating and drinking can’t be allowed.

constraint forall(t in TIME)(not consumes(t)); 

% Each guard can carry one bowl of food or water in each step: from bank to boat, or boat to
% bank. 
constraint forall(t in TIME)(abs(move_food[t]) + abs(move_water[t]) <= G);

% All the movements in the same step have to be in the same direction, 
% either from bank to boat, or boat to bank.
predicate same_direction(TIME: t) = 
    (move_food[t] >= 0 /\ move_water[t] >= 0) \/
    (move_food[t] <= 0 /\ move_water[t] <= 0);    
    
constraint forall(t in TIME)(same_direction(t));

% The aim is to get the elephant onto the boat, with no food or water left in the boat in the least
% number of steps, and no more than a given T time steps. 
constraint elephant[end] = boat;
%constraint forall(t in end..T)(elephant[t] = elephant[t-1]);
constraint water[end, boat] = 0;
constraint food[end, boat] = 0;

% Note that no water or food should be moved after the end step (when the elephant’s weight is
% marked on the boat).
constraint forall(t in end+1..T)(move_food[t] = 0);
constraint forall(t in end+1..T)(move_water[t] = 0);

%solve satisfy; 
solve minimize end;

/*
a solution might be
move_food = [0, 3, -2, -1, 0, 0, 0, 0, 0, 0];
move_water = [3, 0, -1, -2, 0, 0, 0, 0, 0, 0];
end = 4;
*/

