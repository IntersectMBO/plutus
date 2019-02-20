# Public ALB

# Security Group
resource "aws_security_group" "public_alb" {
  vpc_id = "${aws_vpc.plutus.id}"

  ## inbound (world): ICMP 3:4 "Fragmentation Needed and Don't Fragment was Set"
  ingress {
    from_port   = "3"
    to_port     = "4"
    protocol    = "ICMP"
    cidr_blocks = ["0.0.0.0/0"]
  }

  ## inbound (world): https
  ingress {
    from_port   = "443"
    to_port     = "443"
    protocol    = "TCP"
    cidr_blocks = ["0.0.0.0/0"]
  }

  ingress {
    from_port   = "80"
    to_port     = "80"
    protocol    = "TCP"
    cidr_blocks = ["0.0.0.0/0"]
  }

  egress {
    from_port   = "80"
    to_port     = "80"
    protocol    = "TCP"
    cidr_blocks = ["${var.private_subnet_cidrs}"]
  }

  tags {
    Name        = "${var.project}_${var.env}_public_alb"
    Project     = "${var.project}"
    Environment = "${var.env}"
  }
}

data "aws_acm_certificate" "kevm_private" {
  domain      = "*.${var.plutus_tld}"
  statuses    = ["ISSUED"]
  most_recent = true
}

data "aws_acm_certificate" "meadow_private" {
  domain      = "*.${var.meadow_tld}"
  statuses    = ["ISSUED"]
  most_recent = true
}

# An ALB requires multiple availability zones but for now we only
# need 1 availability zone. We will use a classic load balancer now
# and then move to an ALB if we use more AZs later

resource "aws_elb" "plutus" {
  name        = "${var.env}-plutus-lb"
  subnets = ["${aws_subnet.public.*.id}"]
  security_groups = ["${aws_security_group.public_alb.id}"]

  listener {
    instance_port     = 80
    instance_protocol = "http"
    lb_port           = 80
    lb_protocol       = "http"
  }

  listener {
    instance_port      = 80
    instance_protocol  = "http"
    lb_port            = 443
    lb_protocol        = "https"
    ssl_certificate_id = "${data.aws_acm_certificate.kevm_private.arn}"
  }

  health_check {
    healthy_threshold   = 2
    unhealthy_threshold = 2
    timeout             = 3
    target              = "HTTP:80/"
    interval            = 30
  }

  instances                   = ["${aws_instance.playground_a.id}", "${aws_instance.playground_b.id}"]
  cross_zone_load_balancing   = false
  idle_timeout                = 400
  connection_draining         = true
  connection_draining_timeout = 400

  tags {
    Name        = "${var.project}_${var.env}_public_alb"
    Project     = "${var.project}"
    Environment = "${var.env}"
  }
}

resource "aws_route53_record" "alb" {
  zone_id = "${var.plutus_public_zone}"
  name    = "${var.env}.${var.plutus_tld}"
  type    = "A"

  alias {
    name                   = "${aws_elb.plutus.dns_name}"
    zone_id                = "${aws_elb.plutus.zone_id}"
    evaluate_target_health = true
  }
}


resource "aws_elb" "meadow" {
  name        = "${var.env}-meadow-lb"
  subnets = ["${aws_subnet.public.*.id}"]
  security_groups = ["${aws_security_group.public_alb.id}"]

  listener {
    instance_port     = 80
    instance_protocol = "http"
    lb_port           = 80
    lb_protocol       = "http"
  }

  listener {
    instance_port      = 80
    instance_protocol  = "http"
    lb_port            = 443
    lb_protocol        = "https"
    ssl_certificate_id = "${data.aws_acm_certificate.meadow_private.arn}"
  }

  health_check {
    healthy_threshold   = 2
    unhealthy_threshold = 2
    timeout             = 3
    target              = "HTTP:80/"
    interval            = 30
  }

  instances                   = ["${aws_instance.meadow_a.id}", "${aws_instance.meadow_b.id}"]
  cross_zone_load_balancing   = false
  idle_timeout                = 400
  connection_draining         = true
  connection_draining_timeout = 400

  tags {
    Name        = "${var.project}_${var.env}_meadow_alb"
    Project     = "${var.project}"
    Environment = "${var.env}"
  }
}

resource "aws_route53_record" "alb_meadow" {
  zone_id = "${var.meadow_public_zone}"
  name    = "${var.env}.${var.meadow_tld}"
  type    = "A"

  alias {
    name                   = "${aws_elb.meadow.dns_name}"
    zone_id                = "${aws_elb.meadow.zone_id}"
    evaluate_target_health = true
  }
}

## Use this ALB config if we want to switch to an ALB

#resource "aws_alb" "plutus" {
#  subnets = ["${aws_subnet.public.*.id}"]
#
#  security_groups = ["${aws_security_group.public_alb.id}"]
#  internal        = false
#
#  tags {
#    Name        = "${var.project}_${var.env}_public_alb"
#    Project     = "${var.project}"
#    Environment = "${var.env}"
#  }
#
#  # access_logs {
#  #   bucket = "${var.s3_bucket}"
#  #   prefix = "ELB_logs"
#  # }
#}
#
#resource "aws_alb_listener" "playground" {
#  load_balancer_arn = "${aws_alb.plutus.arn}"
#  port              = "443"
#  protocol          = "HTTPS"
#  certificate_arn   = "${data.aws_acm_certificate.kevm_private.arn}"
#
#  default_action {
#    target_group_arn = "${aws_alb_target_group.playground.arn}"
#    type             = "forward"
#  }
#}
#
#resource "aws_alb_target_group" "playground" {
#  port     = "80"
#  protocol = "HTTP"
#  vpc_id   = "${aws_vpc.plutus.id}"
#
#  # health_check {
#  #   path = "/healthcheck"
#  # }
#}
#
#resource "aws_alb_listener_rule" "playground" {
#  depends_on   = ["aws_alb_target_group.playground"]
#  listener_arn = "${aws_alb_listener.playground.arn}"
#  priority     = 100
#
#  action {
#    type             = "forward"
#    target_group_arn = "${aws_alb_target_group.playground.id}"
#  }
#
#  condition {
#    field  = "path-pattern"
#    values = ["*"]
#  }
#}
#
#resource "aws_alb_target_group_attachment" "playground_a" {
#  target_group_arn = "${aws_alb_target_group.playground.arn}"
#  target_id        = "${aws_instance.playground_a.id}"
#  port             = "80"
#}
#
#resource "aws_route53_record" "alb" {
#  zone_id = "Z3HMYGFV3CT1GJ"
#  name    = "${var.env}.${var.tld}"
#  type    = "A"
#
#  alias {
#    name                   = "${aws_alb.plutus.dns_name}"
#    zone_id                = "${aws_alb.plutus.zone_id}"
#    evaluate_target_health = true
#  }
#}
