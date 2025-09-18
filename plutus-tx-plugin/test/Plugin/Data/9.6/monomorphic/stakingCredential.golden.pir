let
  Credential = all a. a -> a
  data StakingCredential | StakingCredential_match where
    StakingHash : Credential -> StakingCredential
    StakingPtr : StakingCredential
in
StakingPtr