# Users that were created elsewhere and needed to be imported

module "christos_loverdos" {
  source     = "../modules/existing-user"
  username   = "christos.loverdos"
  policy_arn = "arn:aws:iam::aws:policy/AdministratorAccess"
}

module "radek_tkaczyk" {
  source     = "../modules/existing-user"
  username   = "radek.tkaczyk"
  policy_arn = "arn:aws:iam::aws:policy/AdministratorAccess"
}

module "kris_jenkins" {
  source     = "../modules/existing-user"
  username   = "kris.jenkins"
  policy_arn = "arn:aws:iam::aws:policy/AdministratorAccess"
}

module "alexander_nemish" {
  source     = "../modules/existing-user"
  username   = "alexander.nemish"
  policy_arn = "arn:aws:iam::aws:policy/AdministratorAccess"
}


# Users that are in the AWS account but that I am unable to import

# module "sam_leathers" {
#   source     = "../modules/existing-user"
#   username   = "sam.leathers"
#   policy_arn = "arn:aws:iam::aws:policy/AdministratorAccess"
# }

# module "serge_kosyrev" {
#   source     = "../modules/existing-user"
#   username   = "serge.kosyrev"
#   policy_arn = "arn:aws:iam::aws:policy/AdministratorAccess"
# }

# Users managed in this terraform instance from the beginning
module "hernan_rajchert" {
  source     = "../modules/user"
  username   = "hernan.rajchert"
  policy_arn = "arn:aws:iam::aws:policy/AdministratorAccess"
}

module "amyas_merivale" {
  source     = "../modules/user"
  username   = "amyas.merivale"
  policy_arn = "arn:aws:iam::aws:policy/AdministratorAccess"
}

module "tobias_pflug" {
  source     = "../modules/user"
  username   = "tobias.pflug"
  policy_arn = "arn:aws:iam::aws:policy/AdministratorAccess"
}
