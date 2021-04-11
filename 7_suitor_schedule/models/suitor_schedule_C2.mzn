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

/* submission on 11.04., 17:13 (suitor_schedule_C2.mzn): 30/42 points
passed A1 (obj=8), A2 (obj=8), B1 (obj=8), B2 (obj=26), C1
passed models A and B

did not pass C2 and model C: kungfu session does not align with the end of any meeting!
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
%array[KUNGFU] of var int: kungfu;  % start time for each lesson
array[KUNGFU] of var 0..24*ndays+1: kungfu;  % start time for each lesson
% unused kungfu lessons have start times after 24*ndays

include "globals.mzn";


% number of jobs: meetings plus blocked time per room
int: numjobs = n + 2*ndays + ndays;
set of int: JOB = 1..numjobs;

% resources: rooms
predicate cum(ROOM: r) = 
    let {
        array[JOB] of var TIME: startx = 
                                start ++ 
                                [(d-1)*24 | d in DAY] ++ 
                                [(d-1)*24 + usedstart[r] | d in DAY] ++
                                [(d-1)*24 + latest | d in DAY];
        array[JOB] of var TIME: durx = 
                                dur ++ 
                                [earliest | d in DAY] ++ 
                                [useddur[r] | d in DAY] ++
                                [24 - latest | d in DAY];
        array[JOB] of var 0..1: res = 
                                % col(assignment, r) ++ 
                                [if room[m] = r then 1 else 0 endif | m in MEETING] ++ 
                                [1 | d in DAY] ++
                                [1 | d in DAY] ++
                                [1 | d in DAY];
    } in cumulative(startx, durx, res, 1);
    
constraint forall(r in ROOM)(cum(r));

% resources: Sun
constraint cumulative(start, dur, [1 | m in MEETING], 1);

% meeting durations are not fixed! they have a min/max depending on suitor and room.
constraint forall(m in MEETING)
                 (dur[m] >= mintime[suitor[m], room[m]] /\
                  dur[m] <= maxtime[suitor[m], room[m]]);

% move time
predicate time_between(var STIME: s1, var STIME: d1, var STIME: s2, var STIME: gap) = 
  s1 + d1 + gap <= s2;  

constraint stage in {B, C} -> forall(m1, m2 in MEETING)
   (start[m1] < start[m2] -> 
   time_between(start[m1], dur[m1], start[m2], move[room[m1], room[m2]]));


% symmetry breaking
constraint forall(m1, m2 in MEETING where m1 < m2) (
    suitor[m1] = suitor[m2] -> start[m1] > start[m2]);
    
% kungfu is ordered
constraint forall(t in 1..n-1)(kungfu[t] <= kungfu[t+1]);

% map kungfu to meeting or past scedule
set of int: KUNGFU0 = 0..n;
array[MEETING] of var KUNGFU0: m2k;
set of int: MEETING0 = 0..n;
array[KUNGFU] of var MEETING0: k2m;
constraint forall(m in MEETING, k in KUNGFU)(m2k[m] = k <-> k2m[k] = m);

% kungfu can happend at begin or end of meeting
array[KUNGFU] of var 0..1: kungfu_at_end;

% stages A and B
constraint stage in {A, B} -> forall(k in KUNGFU)(kungfu[k] = 1 + 24*ndays /\ k2m[k] = 0);

% stage C
constraint stage = C -> forall(k in KUNGFU)
  (kungfu[k] = if 
                 k2m[k] > 0 
               then 
                 % start of kungfu at so that at begin or end of meeting
                 start[k2m[k]] + kungfu_at_end[k] * (dur[k2m[k]] - lessontime)
               else 
                 % start after planning period
                 1 + 24*ndays 
               endif);

% separation between kungfu sessions
constraint forall(k in 1..n-1 where kungfu[k] < 24*ndays)
  (kungfu[k] + lessontime + minsep <= kungfu[k+1]);
  
% meetings must fulfil minimum time requirements
constraint forall(m in MEETING where m2k[m] > 0)
    (dur[m] - lessontime >= mintime[suitor[m], room[m]]);
 

% Solution
% the objective value which is 100 for each kung fu lesson scheduled in the given 
% ndays plus the number of hours of meetings scheduled for Liu Bei
int: omin = count(SUITOR, LiuBei)*min(row(mintime, LiuBei));
int: omax = count(SUITOR, LiuBei)*max(row(maxtime, LiuBei)) + n*100;
var 0..omax: obj = sum(i in MEETING where suitor[i] = LiuBei)(dur[i])
                 - lessontime * count(m in MEETING)(suitor[m] = LiuBei /\ m2k[m] > 0)
                 + 100 * count(m in MEETING)(m2k[m] > 0);
solve maximize obj;


% array[ROOM] of string: sroom = ["R", "G", "B"];

% predicate room_booked(TIME: t, ROOM: r) = 
%   let {TIME: dt = t mod 24;} in
%   dt < earliest \/ 
%   dt >= latest \/
%   (dt >= usedstart[r] /\ dt < usedstart[r] + useddur[r]) ;


% array[STIME] of var 0..n: X;
% constraint forall(i in MEETING, t in STIME)
%                  (start[i] <= t /\ start[i] + dur[i] > t <-> X[t] = i);  

output ["start = \(start);\n"] ++
       ["dur = \(dur);\n"] ++
       ["room = \(room);\n"] ++
       ["kungfu = \(kungfu);\n"] ++
%        ["suitor = \(suitor);\n"] ++
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
