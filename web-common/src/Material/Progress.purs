module Material.Progress where

data Progress
  = Progress0
  | Progress10
  | Progress20
  | Progress30
  | Progress40
  | Progress50
  | Progress60
  | Progress70
  | Progress80
  | Progress90
  | Progress100
  | Indeterminate

progressClass :: Progress -> String
progressClass Progress0 = "progress-0"

progressClass Progress10 = "progress-10"

progressClass Progress20 = "progress-20"

progressClass Progress30 = "progress-30"

progressClass Progress40 = "progress-40"

progressClass Progress50 = "progress-50"

progressClass Progress60 = "progress-60"

progressClass Progress70 = "progress-70"

progressClass Progress80 = "progress-80"

progressClass Progress90 = "progress-90"

progressClass Progress100 = "progress-100"

progressClass Indeterminate = "progress-indeterminate"
