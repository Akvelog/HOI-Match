####################################################################
#
#    This file was generated using Parse::Yapp version 1.05.
#
#        Don't edit this file, use source file instead.
#
#             ANY CHANGE MADE HERE WILL BE LOST !
#
####################################################################
package HOI::typeparser;
use vars qw ( @ISA );
use strict;

@ISA= qw ( Parse::Yapp::Driver );
use Parse::Yapp::Driver;



sub new {
        my($class)=shift;
        ref($class)
    and $class=ref($class);

    my($self)=$class->SUPER::new( yyversion => '1.05',
                                  yystates =>
[
	{#State 0
		ACTIONS => {
			'IDENT' => 3,
			'NIL' => 1
		},
		GOTOS => {
			'Type' => 2,
			'Types' => 4
		}
	},
	{#State 1
		DEFAULT => -5
	},
	{#State 2
		ACTIONS => {
			'CONCAT' => 5,
			'COMMA' => 6
		},
		DEFAULT => -1
	},
	{#State 3
		ACTIONS => {
			'LPAREN' => 7
		},
		DEFAULT => -3
	},
	{#State 4
		ACTIONS => {
			'' => 8
		}
	},
	{#State 5
		ACTIONS => {
			'NIL' => 1,
			'IDENT' => 3
		},
		GOTOS => {
			'Type' => 9
		}
	},
	{#State 6
		ACTIONS => {
			'IDENT' => 3,
			'NIL' => 1
		},
		GOTOS => {
			'Type' => 2,
			'Types' => 10
		}
	},
	{#State 7
		ACTIONS => {
			'NIL' => 1,
			'IDENT' => 3
		},
		DEFAULT => -7,
		GOTOS => {
			'Type' => 11,
			'Typelist' => 12
		}
	},
	{#State 8
		DEFAULT => 0
	},
	{#State 9
		ACTIONS => {
			'CONCAT' => 5
		},
		DEFAULT => -4
	},
	{#State 10
		DEFAULT => -2
	},
	{#State 11
		ACTIONS => {
			'NIL' => 1,
			'CONCAT' => 5,
			'IDENT' => 3
		},
		DEFAULT => -7,
		GOTOS => {
			'Typelist' => 13,
			'Type' => 11
		}
	},
	{#State 12
		ACTIONS => {
			'RPAREN' => 14
		}
	},
	{#State 13
		DEFAULT => -8
	},
	{#State 14
		DEFAULT => -6
	}
],
                                  yyrules  =>
[
	[#Rule 0
		 '$start', 2, undef
	],
	[#Rule 1
		 'Types', 1,
sub
#line 10 "typeparser.yp"
{ [ $_[1] ] }
	],
	[#Rule 2
		 'Types', 3,
sub
#line 11 "typeparser.yp"
{ my $sublist = $_[3]; my @list= ($_[1], @$sublist); \@list }
	],
	[#Rule 3
		 'Type', 1,
sub
#line 14 "typeparser.yp"
{ { "kind" => "any", "val" => $_[1] } }
	],
	[#Rule 4
		 'Type', 3,
sub
#line 15 "typeparser.yp"
{ { "kind" => "list", "val" => [ $_[1], $_[3] ] } }
	],
	[#Rule 5
		 'Type', 1,
sub
#line 16 "typeparser.yp"
{ { "kind" => "list", "val" => [] } }
	],
	[#Rule 6
		 'Type', 4,
sub
#line 17 "typeparser.yp"
{ { "kind" => "adt", "val" => [ $_[1], $_[3] ] } }
	],
	[#Rule 7
		 'Typelist', 0,
sub
#line 20 "typeparser.yp"
{ [] }
	],
	[#Rule 8
		 'Typelist', 2,
sub
#line 21 "typeparser.yp"
{ my $sublist = $_[2]; my @list= ($_[1], @$sublist); \@list }
	]
],
                                  @_);
    bless($self,$class);
}

#line 24 "typeparser.yp"


1;
