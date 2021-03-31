{ keys }:
{
  kris = { region = "eu-west-1"; keys = [ keys.kris ]; };
  alpha = { region = "eu-west-2"; keys = with keys; [ kris pablo hernan tobias amyas ]; };
  pablo = { region = "eu-west-3"; keys = [ keys.pablo ]; };
  playground = { region = "us-west-1"; keys = with keys; [ kris pablo hernan tobias amyas ]; };
  testing = { region = "eu-west-3"; keys = with keys; [ kris pablo hernan tobias amyas quanterall ]; };
  hernan = { region = "us-west-2"; keys = [ keys.hernan ]; };
  tobias = { region = "eu-west-1"; keys = [ keys.tobias ]; };
  amyas = { region = "eu-west-2"; keys = [ keys.amyas ]; };
}
