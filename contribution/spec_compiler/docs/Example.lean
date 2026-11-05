import RegionExamples

open Contribution.RegionCompiler
open Contribution.RegionCompiler.Examples

#eval checkNormalized units disconnected (point (4/5))
-- false: physical x = 18, an excluded boundary

#eval checkNormalized units disconnected (point (9/10))
-- true: physical x = 19

#eval checkNormalized units disconnected
  (point (13421773/16777216))
-- true: the exact float32 value of 0.8 is greater than 4/5
