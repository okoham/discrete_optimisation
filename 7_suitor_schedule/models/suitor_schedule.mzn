% models for submission, time limit 60 s each: 
% A0, A3, B2, B4, C1, C3

% Idea 1: use a next construct, like in the channel example
% Idea 2: three workers (one for each room), each has a capacity 1, then use cumulative. 
%         can incorporate fixed tasks into that.

% multiple (unary) resources
% think of it as assigning tasks to workers. Each of the worker is a unary resource. They
% (notionally) work on all tasks but the ones they are not assigned are given a resource usage 
% of 0. The ones they do work on have a resource usage of 1. They have the capacity of working 
% on one task. This can be encoded with cumulative. Add the times of unavailability of each
% worker as tasks with fixed start time and duration and resource usage of 1. These tasks only 
% appear in the cumulative constraint for that worker.

% next works better than order/argsort

/* submission on 05.04., 07:35:
passed A1 (obj=8), A2 (obj=8), B1 (obj=8), B2 (obj=26)
*/

% scheduling suitors
enum SUITOR;
SUITOR: LiuBei; % which suitor is LiuBei
int: n; % number of meetings
set of int: MEETING = 1..n;
array[MEETING] of SUITOR: suitor;

enum ROOM = { Red, Gold, Blue };
array[SUITOR,ROOM] of int: mintime;
array[SUITOR,ROOM] of int: maxtime;
constraint forall(s in SUITOR, r in ROOM)
                 (assert(mintime[s,r] >= 1 /\ maxtime[s,r] >= mintime[s,r],
                  "error in mintime/maxtime at [\(s),\(r)]\n"));

array[ROOM,ROOM] of int: move;
constraint forall(r in ROOM)(assert(move[r,r] = 0,"move[\(r),\(r)] != 0\n"));

int: ndays; % number of days
set of int: DAY = 1..ndays;
int: earliest; % time for earliest meeting start
int: latest;  % time for end of latest meeting

int: lessontime; % time for kung fu lesson;
int: minsep;     % minimum time between consecutive kung fu lessons

array[ROOM] of int: usedstart;  % time others use each room each day
array[ROOM] of int: useddur;    % durations of others use

enum STAGE = {A,B,C};
STAGE: stage;

set of int: TIME = 0..24*ndays; % only start times, or also end times???
set of int: STIME = 0..24*ndays-1;

array[MEETING] of var STIME: start;
array[MEETING] of var TIME: dur;    % duration in false schedule
array[MEETING] of var ROOM: room;
set of int: KUNGFU = 1..n;
array[KUNGFU] of var int: kungfu;  % start time for each lesson
% unused kungfu lessons have start times after 24*ndays

include "globals.mzn";

% temporary workaround for kungfu
constraint stage in {A, B} /\ forall(k in KUNGFU)(kungfu[k] = 1 + 24*ndays);

% dummy meetings and next array ersect
% int: nr = card(ROOM);

% number of jobs: meetings plus blocked time per room
int: numjobs = n + 2*ndays + ndays;
set of int: JOB = 1..numjobs;
array[MEETING, ROOM] of var 0..1: assignment;
constraint forall(m in MEETING, r in ROOM)(assignment[m,r] = 1 <-> room[m] = r);
constraint forall(m in MEETING)(sum(r in ROOM)(assignment[m,r]) = 1);
%array[JOB] of var 0..1: resource = [1 | x in JOB]; % one resource - Sun? Needed at all?

predicate cum(ROOM: r) = 
    let {
        array[JOB] of var TIME: startx = start ++ 
                                [(d-1)*24 | d in DAY] ++ 
                                [(d-1)*24 + usedstart[r] | d in DAY] ++
                                [(d-1)*24 + latest | d in DAY];
        array[JOB] of var TIME: durx = dur ++ 
                                [earliest | d in DAY] ++ 
                                [useddur[r] | d in DAY] ++
                                [24 - latest | d in DAY];
        array[JOB] of var TIME: res = col(assignment, r) ++ 
                                [1 | d in DAY] ++
                                [1 | d in DAY] ++
                                [1 | d in DAY];
    } in cumulative(startx, durx, res, 1);
    
constraint forall(r in ROOM)(cum(r));


% meeting durations are not fixed! they have a min/max depending on suitor and room.
constraint forall(m in MEETING)
                 (dur[m] >= mintime[suitor[m], room[m]] /\
                  dur[m] <= maxtime[suitor[m], room[m]]);

% no - the unary resource is Sun. We can't have parallel meetings. 
% but there are other resources using the rooms at fixed times. how to deal with that?

%
% Ensure that there is no overlap between two jobs
%
predicate nonoverlap(var int: s1, var int: d1, var int: s2, var int: d2) =
    s1 + d1 <= s2 \/ s2 + d2 <= s1;
          
% 
% Precedences: job1 must be done before job2
% 
predicate prec(int: job1, int: job2, 
               array[int] of var int: start, 
               array[int] of var int: dur) = 
    start[job1] + dur[job1] <= start[job2];


% earliest start / latest end 
% constraint forall(m in MEETING)
%                  (let {var int: d = start[m] div 24;} in
%                  start[m] >= 24*d + earliest /\ 
%                  (start[m] + dur[m]) <= 24*d + latest);



% basic stuff
% constraint 
%     cumulative(start, dur, resource, nr)
           
%     /\ % assignments
%     forall(m in MEETING) (
%         resource[m] = sum(r in ROOM)(assignment[m,r] = 1) 
%         /\
%         % if a room is assigned to two meetings, these meetings cannot overlap
%         forall(m2 in MEETING where m < m2) (
%             exists(r in ROOM) (assignment[m,r] + assignment[m2,r] = 2)
%                 -> nonoverlap(start[m], dur[m], start[m2], dur[m2]))
%         /\
%         % if resources of two jobs > total then they cannot overlap
%         forall(m2 in MEETING where m < m2) (
%             if resource[m] + resource[m2] > nr then
%                 nonoverlap(start[m], dur[m], start[m2], dur[m2])
%             else
%                 true
%             endif)
%     );


% TODO: can we include this into the disjunctive?
% include "disjunctive.mzn";
% constraint disjunctive(start, dur);

predicate time_between(var STIME: s1, var STIME: d1, var STIME: s2, var STIME: gap) = 
  s1 + d1 + gap <= s2;  

% constraint stage in {B, C} -> forall(m in MEETING where next[m] != dummy)
%    (time_between(start[m], dur[m], start[next[m]], move[room[m], room[next[m]]]));
% constraint stage = A -> forall(m1, m2 in MEETING)
%    (start[m1] < start[m2] -> 
%    time_between(start[m1], dur[m1], start[m2], ));

constraint stage in {B, C} -> forall(m1, m2 in MEETING)
   (start[m1] < start[m2] -> 
   time_between(start[m1], dur[m1], start[m2], move[room[m1], room[m2]]));

% constraint stage in {B, C} -> forall(j in 1..n-1)
%     (let {
%         var MEETING: i1 = order[j];
%         var MEETING: i2 = order[j+1]; 
%     } in 
%   time_between(start[i1], dur[i1], start[i2], move[room[i1], room[i2]]));

% predicate freeroom(var TIME: begin, var int: duration, var ROOM: r) = 
%   let {
%     var int: sm = begin mod 24;
%   } in %nonoverlap(sm, duration, 0, earliest) /\
%        %nonoverlap(sm, duration, latest, 24-latest) /\
%        nonoverlap(sm, duration, usedstart[r], useddur[r]);

% constraint forall(i in MEETING)(freeroom(start[i], dur[i], room[i]));

% symmetry breaking
constraint forall(m1, m2 in MEETING where m1 < m2) (
    suitor[m1] = suitor[m2] -> start[m1] < start[m2]);

% Solution
% the objective value which is 100 for each kung fu lesson scheduled in the given 
% ndays plus the number of hours of meetings scheduled for Liu Bei
% range: n*max(maxtime) + n*100
% TODO for stage C: subtract kungfu time from liubei time
int: omin = count(SUITOR, LiuBei)*min(row(mintime, LiuBei));
int: omax = count(SUITOR, LiuBei)*max(row(maxtime, LiuBei)) + n*100;
var 0..omax: obj = sum(i in MEETING where suitor[i] = LiuBei)(dur[i]);
solve maximize obj;


array[ROOM] of string: sroom = ["R", "G", "B"];

predicate room_booked(TIME: t, ROOM: r) = 
  let {TIME: dt = t mod 24;} in
  dt < earliest \/ 
  dt >= latest \/
  (dt >= usedstart[r] /\ dt < usedstart[r] + useddur[r]) ;


array[STIME] of var 0..n: X;
constraint forall(i in MEETING, t in STIME)
                 (start[i] <= t /\ start[i] + dur[i] > t <-> X[t] = i);  

output ["start = \(start);\n"] ++
       ["dur = \(dur);\n"] ++
       ["room = \(room);\n"] ++
       ["kungfu = \(kungfu);\n"] ++
       %["suitor = \(suitor);\n"] ++
%        ["order = \(order);\n"] ++
%        ["next = \(next);\n"] ++
       ["obj = \(obj);\n"]  ++

%        ["\n"] ++
%        ["  t D     H RBL ii SU RM\n"] ++
%        [if true then % t mod 24 in earliest-1..latest then
%           show_int(3, t) ++ 
%           show_int(2, 1 + t div 24) ++ 
%           show_int(3, t mod 24) ++ "-" ++ show_int(2, 1 + t mod 24) ++
%           " " ++ concat([if room_booked(t, r) then sroom[r] else "." endif | r in ROOM]) ++
%           if fix(X[t] > 0) then show_int(3, X[t]) else "   " endif ++   % meeting number
%           if fix(X[t] > 0) then " " ++ show(suitor[X[t]]) else "  " endif ++
%           if fix(X[t] > 0) then " " ++ show(room[X[t]]) else "    " endif ++
%           "\n"
%         else "" endif
%         | t in STIME] ++

       [];
