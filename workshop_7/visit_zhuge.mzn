enum PERSON; % set of people to be visited

array[PERSON] of int: duration;    % duration of visit
array[PERSON] of bool: on_weekend; % can the person be visited over weekends
array[PERSON] of int: rank;        % rank of person

array[int,1..2] of PERSON: prec;   % precedences between visits
set of int: PREC = index_set_1of2(prec); 

0..6: starting_day; % which day of the week is day 0 in the schedule
                    % 0 Monday, 1 Tuesday, ..., 5 Saturday, 6 Sunday

% upper bound on the amount of time needed: total duration plus 1 week
% per person who cant be visited on the weekend
int: total = sum(duration) + 7*sum(p in PERSON)(on_weekend[p] = false);
set of int: TIME = 0..total;

array[PERSON] of var TIME: start;
var TIME: end = max(p in PERSON)(start[p] + duration[p]);

% precedences
constraint forall(i in PREC)
                 (start[prec[i,1]] + duration[prec[i,1]] <= start[prec[i,2]]);
       
% limited resources: Liu Bei is the unique resource
include "disjunctive.mzn";
constraint disjunctive(start, duration);

% weekend constraint
% day_of_week = (t + starting_day) mod 7
constraint forall(p in PERSON)
           (not on_weekend[p] -> forall(t in 0..duration[p]-1)
                                       (let {var 0..6: dow = (start[p] + starting_day + t) mod 7} in 
                                       dow in {0, 1, 2, 3, 4})
           );
% in the solution video, they did this differently. They created additional tasks (weekend tasks),
% and assigned them to the people who can't be visited on weekends, then created another disjunctive
% constraint.

% rank violations
% compare all pairs of persons. count instances where start[p1] < start[p2] and rank[p1] > rank[p2]
var int: rank_violation;
rank_violation = count(p1, p2 in PERSON)
                      (start[p1] < start[p2] /\ rank[p1] > rank[p2]);

% solve    
% solve minimize end;
% in the solution video, the minimised card(PERSON)*card(PERSON)*end + rank_violation
% as multiplier, use any number that is big enough (> max possible value of rank violation).
% with this approach, we always minimise ent time before worrying about rank violations
solve minimize card(PERSON)*card(PERSON)*end + rank_violation;

% output 
output ["start = \(start);\nend = \(end);\nrank_violation = \(rank_violation);\n"];