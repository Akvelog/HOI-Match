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
			'NIL' => 3,
			'CONST' => 5,
			'IDENT' => 2
		},
		GOTOS => {
			'Types' => 1,
			'Type' => 4
		}
	},
	{#State 1
		ACTIONS => {
			'' => 6
		}
	},
	{#State 2
		ACTIONS => {
			'LPAREN' => 7
		},
		DEFAULT => -4
	},
	{#State 3
		DEFAULT => -6
	},
	{#State 4
		ACTIONS => {
			'CONCAT' => 8,
			'COMMA' => 9
		},
		DEFAULT => -1
	},
	{#State 5
		DEFAULT => -3
	},
	{#State 6
		DEFAULT => 0
	},
	{#State 7
		ACTIONS => {
			'IDENT' => 2,
			'NIL' => 3,
			'CONST' => 5
		},
		DEFAULT => -8,
		GOTOS => {
			'Typelist' => 10,
			'Type' => 11
		}
	},
	{#State 8
		ACTIONS => {
			'NIL' => 3,
			'CONST' => 5,
			'IDENT' => 2
		},
		GOTOS => {
			'Type' => 12
		}
	},
	{#State 9
		ACTIONS => {
			'IDENT' => 2,
			'NIL' => 3,
			'CONST' => 5
		},
		GOTOS => {
			'Type' => 4,
			'Types' => 13
		}
	},
	{#State 10
		ACTIONS => {
			'RPAREN' => 14
		}
	},
	{#State 11
		ACTIONS => {
			'NIL' => 3,
			'CONST' => 5,
			'IDENT' => 2,
			'CONCAT' => 8
		},
		DEFAULT => -8,
		GOTOS => {
			'Type' => 11,
			'Typelist' => 15
		}
	},
	{#State 12
		ACTIONS => {
			'CONCAT' => 8
		},
		DEFAULT => -5
	},
	{#State 13
		DEFAULT => -2
	},
	{#State 14
		DEFAULT => -7
	},
	{#State 15
		DEFAULT => -9
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
#line 11 "typeparser.yp"
{ [ $_[1] ] }
	],
	[#Rule 2
		 'Types', 3,
sub
#line 12 "typeparser.yp"
{ my $sublist = $_[3]; my @list= ($_[1], @$sublist); \@list }
	],
	[#Rule 3
		 'Type', 1,
sub
#line 15 "typeparser.yp"
{ { "kind" => "const", "val" => $_[1] } }
	],
	[#Rule 4
		 'Type', 1,
sub
#line 16 "typeparser.yp"
{ { "kind" => "any", "val" => $_[1] } }
	],
	[#Rule 5
		 'Type', 3,
sub
#line 17 "typeparser.yp"
{ { "kind" => "list", "val" => [ $_[1], $_[3] ] } }
	],
	[#Rule 6
		 'Type', 1,
sub
#line 18 "typeparser.yp"
{ { "kind" => "list", "val" => [] } }
	],
	[#Rule 7
		 'Type', 4,
sub
#line 19 "typeparser.yp"
{ { "kind" => "adt", "val" => [ $_[1], $_[3] ] } }
	],
	[#Rule 8
		 'Typelist', 0,
sub
#line 22 "typeparser.yp"
{ [] }
	],
	[#Rule 9
		 'Typelist', 2,
sub
#line 23 "typeparser.yp"
{ my $sublist = $_[2]; my @list= ($_[1], @$sublist); \@list }
	]
],
                                  @_);
    bless($self,$class);
}

#line 26 "typeparser.yp"


1;
