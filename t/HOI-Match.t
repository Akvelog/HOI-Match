# Before 'make install' is performed this script should be runnable with
# 'make test'. After 'make install' it should work as 'perl HOI-Match.t'

#########################

use strict;
use warnings;

use Test::More tests => 5;
BEGIN { use_ok('HOI::Match') };

#########################

sub sum {
    HOI::Match::pmatch(
        "h :: r" => sub { my %args = @_; $args{h} + sum($args{r}) },
        "nil" => sub { 0 }
    )->(@_)
}
ok(sum([1, 2, 3, 4]) == 10);

sub head {
    HOI::Match::pmatch(
        "h :: _" => sub { my %args = @_; $args{h} }
    )->(@_)
}
my $res_head = head([1, 2, 3]);
ok(head([1, 2, 3]) == 1);

sub tail {
    HOI::Match::pmatch(
        "_ :: r" => sub { my %args = @_; $args{r} }
    )->(@_)
}
my $res_tail = tail([1, 2, 3]);
is_deeply($res_tail, [2, 3]);

sub point_extract {
    HOI::Match::pmatch(
        "point (x _) :: r" => sub { my %args = @_; $args{x} + point_extract($args{r}) },
        "nil" => sub { 0 }
    )->(@_)
}
ok(
    point_extract(
        [ 
            {"type" => "point", "val" => [ 1, 2 ]},
            {"type" => "point", "val" => [ 2, 4 ]},
            {"type" => "point", "val" => [ 3, 6 ]},
        ]
    ) == 6
);
