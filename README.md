# Microc

Microc (pronounced micro-see) is a compiler, written in Rust, for a toy programming language called **Micro** ([tokens](https://github.com/jkshtj/Microc/blob/master/token_definitions.txt) and [grammar](https://github.com/jkshtj/Microc/blob/master/grammar.txt)). I did not invent Micro. I took it from the [undergraduate compilers course](https://engineering.purdue.edu/~milind/ece468/2017fall/) in Computer Engineering at Purdue University. 

## Micro

Micro is a simple, statically typed programming language. Its core consists of 3 data types - int, float and string literals (with simple math operations supported on the numeric types), 4 statements - assignment, read, write and return, conditional blocks, for-loops and user-defined functions. 

Micro does not support data aliasing, either in the form of references or pointers. User memory allocation is not supported either. That said, these 2 might be very interesting additions to work on!

A simple valid micro program can be seen below -
```cpp=
PROGRAM fibonacci
BEGIN
    // Globals
    STRING input := "Please input an integer number: ";
    STRING space := " ";
    STRING eol := "\n";

    // User-defined function
    FUNCTION INT F (INT n)
    BEGIN
        // Conditional block
        IF (n > 2)
            RETURN F(n-1)+F(n-2);
        ELSE
            IF (n = 0)     
                RETURN 0;
            ELSE
                IF(n = 1)
                    RETURN 1;
                ELSE
                    RETURN 1;
                FI
            FI
        FI
    END

    // Every valid Micro program, like C, 
    // must have a `main` function.
    FUNCTION VOID main ()
    BEGIN
        INT i, end, result;
        // Output can be written to stdout
        WRITE(input);
        // Input can read from stdin
        READ(end);
        
        // `For` loop
        FOR (i := 0; i != end; i := i + 1)
            result := F(i);
            WRITE (i,space);
            WRITE (result,eol);
        ROF

    END

END
```

## Microc - my Micro implementation

I built Microc in stages, putting in place a compilation pipeline first and then updating components in the pipeline as I incrementally added support for different language features. 

I'd like to go into the details of Microc and document my experience with and understanding of concepts/topics, but before that let me lay out the steps that comprise Microc's compilation pipeline so we have a guidepost for things to talk about.

1. [**Frontend**] Tokenize source code.
2. [**Frontend**] Parse token stream and perform syntax-directed translation to generate the AST.
3. [**Frontend**] Traverse AST to generate [3-Address Code (3AC) intermediate representation (IR)](https://github.com/jkshtj/Microc/blob/30df0a851342bd12d4fdec90d125d366d65ed696/src/three_addr_code_ir/three_address_code.rs#L5) of the source program.
4. [**Middleend**] Convert 3AC IR to a control-flow graph (CFG).
5. [**Middleend**] Perform data-flow analysis, liveness analysis specifically, on the CFG.
6. [**Middleend**] Perform register allocation using the output of liveness analysis.
7. [**Backend**] Lower 3AC representation into [Tiny assembly](https://engineering.purdue.edu/~milind/ece468/2017fall/assignments/step4/tinyDoc.txt). Tiny is a fictional target that feels like a subset of x86.

With the high level compilation steps laid out, let's dive into the details. 

### Tokenizing and Parsing

> Compiler frontend starts here.

As interesting as it might be to write your own tokenizer and parser, my motivation for writing Microc was to get an end to end overview of the compilation process and focus more on the compiler middle and back ends. To that effect I decided to use a parser generator called [LALRPOP](https://github.com/lalrpop/lalrpop). LALRPOP is parser generator for [Look-Ahead Left to Right (LALR)](https://en.wikipedia.org/wiki/LALR_parser) parsers. 

LALRPOP made it fairly easy to generate my AST, by associating actions to each production rule of Micro's grammar. I do not understand parsing theory deep enough to go further into how LALR parsing works, but it's a very well established topic that you can understand using most textbooks on compiler construction.

### AST

As I mentioned in the very beginning, Microc is written in Rust (in fact Rust was the reason I wanted to understand compilers better in the first place)!. 

Having previously implemented a compiler in Java, it was a pleasant experience modeling my AST in Rust! Thanks to [Rust enums](https://doc.rust-lang.org/reference/items/enumerations.html) my AST definition was fairly concise, and thanks to `match` statements over Rust enums, I was able to get statically dispatched AST visitors! Additionally, Rust's [newtype pattern](https://doc.rust-lang.org/rust-by-example/generics/new_types.html) made it easy to create strong domain types and obtain compile time guarantees about the data that was being supplied to the different internal compiler APIs.

Here's what the Rust code for my AST looks.

```rust=
/// Differentiates an addition `Add` node
/// from a subtraction `Add` node.
#[derive(Debug, Copy, Clone)]
pub enum AddOp {
    Add,
    Sub,
}

/// Differentiates an multiplication
/// `Mul` node from a division
/// `Mul` node.
#[derive(Debug, Copy, Clone)]
pub enum MulOp {
    Mul,
    Div,
}

/// Represents the comparison
/// operation in a boolean expression.
#[derive(Debug, Copy, Clone)]
pub enum CmpOp {
    /// Less than
    Lt,
    /// Greater than
    Gt,
    /// Equal to
    Eq,
    /// Not equal to
    Ne,
    /// Less than or equal to
    Lte,
    /// Greater than or equal to
    Gte,
}

/// Represents an identifier
/// for a declared data symbol.
/// `data::Symbol` is a reference-counted
/// pointer (`Rc<T>`) to a symbol
/// stored in the symbol table.
#[derive(Debug, Clone)]
pub struct Identifier {
    pub symbol: data::Symbol,
}

/// Math expressions in Microc
/// that evaluate to a numeric
/// value.
#[derive(Debug, Clone)]
pub enum Expr {
    Id(Identifier),
    IntLiteral(i32),
    FloatLiteral(f64),
    Add {
        op: AddOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Mul {
        op: MulOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Call {
        func_symbol: Rc<function::Symbol>,
        args: Vec<Expr>,
    },
    None,
}

/// An assignment, which exists only
/// for building different statements
/// made up of assign semantics, such as,
/// assign, if and for statements.
#[derive(Debug, Clone)]
pub struct Assignment {
    pub lhs: Identifier,
    pub rhs: Expr,
}

/// A boolean expression that evaluates
/// to either true or false.
#[derive(Debug, Clone)]
pub struct Condition {
    pub cmp_op: CmpOp,
    pub lhs: Expr,
    pub rhs: Expr,
}

/// Statements in Microc.
#[derive(Debug, Clone)]
pub enum Stmt {
    Read(Vec<Identifier>),
    Write(Vec<Identifier>),
    Assign(Assignment),
    If {
        condition: Condition,
        then_block: Vec<Stmt>,
        else_block: Vec<Stmt>,
    },
    For {
        init: Option<Assignment>,
        condition: Condition,
        incr: Option<Assignment>,
        body: Vec<Stmt>,
    },
    // The return statement has been modeled to reflect
    // the reality of Micro more closely. The return statement
    // in Micro is an assignment to a memory location that is
    // created by the caller, on the stack.
    Return(Assignment),
    None,
}

/// Represents constructs in Microc
/// that can be composed from expressions
/// and statements. Currently, the only
/// such valid construct in Microc is
/// functions. But this can change in the
/// future to support classes/structs/enums etc.
#[derive(Debug, Clone)]
pub enum Item {
    Function {
        symbol: Rc<function::Symbol>,
        body: Vec<Stmt>,
    },
}

/// Abstract syntax tree representation
/// for Microc.
#[derive(Debug)]
pub enum AstNode {
    Item(Item),
    Stmt(Stmt),
    Expr(Expr),
}
```

#### AST Visitors

I mentioned I was able to get statically dispatched AST visitors. I wanted to show what that looks like in practice. 

> [Wikipedia](https://en.wikipedia.org/wiki/Visitor_pattern) defines visitor pattern rather well! However, in my own words and in our context -
> 
> Visitor pattern is a common way to decouple operations from a "heterogeneous" type (read as, a type containing different types) over which those operations need to be performed. It can also be thought of as an iterator, but over a collection of different types.
>
> In languages such as Java or C++, that don't support tagged unions or sum types (same thing as Rust enums), visitor pattern is implemented using interfaces/virtual functions and [double dynamic dispatch](https://en.wikipedia.org/wiki/Double_dispatch).

I have the following `Visitor` trait.

```rust=
pub trait Visitor<T> {
    fn visit_item(&mut self, item: Item) -> T;
    fn visit_statement(&mut self, stmt: Stmt) -> T;
    fn visit_expression(&mut self, expr: Expr) -> T;
    
    // [Mistake] - I realized that there was no reason for
    // me to define separate `Assignment` and `Condition` nodes.
    // They could very well be captured by the `Statement` and the
    // `Expression` types.
    fn visit_assignment(&mut self, assigment: Assignment) -> T;
    fn visit_condition(&mut self, condition: Condition) -> T;
}
```

With the `Visitor` trait I can now implement different operations over my AST. For instance, I could have a `PrintNodeVisitor` that just prints each AST node.

```rust=
struct PrintAstNodeVisitor;

impl Visitor<()> for PrintAstNodeVisitor {
    fn visit_expression(&mut self, expr: Expr) -> () {
        match expr {
            Expr::Add { op, lhs, rhs } => {
                self.visit_expression(lhs);
                self.visit_expression(lhs);
                println!("{}{}{}", lhs, op, rhs);
            }
            ...
        }
    }
    ...
}
```

You might be wondering why my `Visitor` trait is generic over `T`. It's because I need to communicate information between nodes, as I traverse the AST. Specifically, I need to communicate the 3AC IR of child nodes to the parent node.

### Lowering to 3AC IR
> Compiler frontend ends here.

With the background and context we set about my AST and AST visitors, this step becomes easy to explain! I implemented an AST visitor that generates 3AC IR for each node of the AST - by the end generating 3AC IR for the entire program, represented by the AST.

Unlike the tree-like structure of the AST, the 3AC IR of a Micro program has a flat structure. This property exists because we want the 3AC IR to be amenable to control-flow and data-flow analysis (more on what each one is in the following sections).

### 3AC to CFG

> Compiler middleend starts here.
> 
> This step onwards, things got very interesting for me because I got an insight into the primitives that make up compiler optimizations!

In this step I convert the 3AC IR for a Micro program into a CFG. **What is a CFG, you ask?** 

A CFG is not very different from a flowchart. In fact it is a flow chart, that just shows the flow of "control", as your program is executed. Each node in the CFG is called a basic-block. A basic block is essentially a block of instructions, where control can enter into the block only at the first instruction and exit only at the last. A CFG is the gateway to most compiler optimizations, both simple and complex.

For a simple C program as below -
```c=
#include <stdio.h>

int main() {
    int n;
    printf("Enter a number: \n");
    scanf("%d", &n);
    
    if (n % 2 == 0) {
        printf("Number is even!");
        return 2;
    } else {
        printf("Number is odd!");
        return 1;
    }
}
```

The CFG will look like -
```
                            | Entry:      |
                            | ----------- |
                            | int n       |
                            | printf(...) |
                            | scanf(...)  |
                            | ----------- |
                            /             \
                           /               \
                          /                 \
                         /                   \
                | BB1:        |         | BB2:        |
                | ----------- |         | ----------- |
                | printf(...) |         | printf(...) |
                | return 2    |         | return 1    |
                | ----------- |         | ----------- |
                     	     \           /
                              \         /
                               \       /
                                \     /
                            | Exit:       |
                            | ----------- |
                            

```

The algorithm to convert the 3AC IR to a CFG is fairly straightforward. I won't go into the details of it and you can see my 3AC to CFG implementation [here](https://github.com/jkshtj/Microc/blob/30df0a851342bd12d4fdec90d125d366d65ed696/src/cfg/basic_block.rs#L227). At a high level, however, we essentially break up the 3AC IR instruction stream into basic blocks, terminating a basic block every time we come across an instruction that is a basic-block terminator - jump, branch, return etc.


### Data-Flow Analysis
> Compiler middleend ends here.

There's a number of compiler optimizations that can be performed right after we have a CFG, such as, dead-code removal, dead-store removal and local value numbering (this is an enabler for other compiler optimizations such as, common sub-expression elimination, constant folding, copy folding etc.). These optimizations, however, are locally scoped - they are applied per basic block and not on the entire CFG.

There's still optimizations that can be performed taking the entire CFG into consideration. These optimizations require different global analyses, which are often framed as data-flow problems. One such global analyses is reaching-definitions (what definitions of a variable `v` reach a given program point), which can help us perform an optimization like constant folding, globally.

In Microc, I perform data-flow analysis to obtain liveness data (what variables are live or dead at a given program point). I then use the liveness data to perform dumb register-allocation (spilling a currently unused register to the stack as needed), for when I lower the 3AC IR to Tiny assembly.

I realized much later after implementing the liveness data-flow analysis that all data-flow analyses can be performed using the same framework. Perhaps, I'll write about it in a separate blog post.

### Lowering to Tiny assembly

> Compiler backend starts and ends here.

While compiler backends can be extremely complex, performing instruction selection, instruction scheduling, advanced register allocation directly on machine code etc., my compiler backend unintentionally ended up being fairly simple :sweat_smile:. 

I more or less, simply map the 3AC IR to Tiny assembly, adding new load/store instructions based on the register allocation data I collected in the previous step.

## Future additions/plans

This project was a tremendous experience in the way of learning compiler construction! But I think, it's still got untapped utility, both for me and for anyone that's interested in compiler construction.

1. We can convert our 3AC IR to LLVM IR. This would be useful for getting your hands dirty with LLVM IR.
2. Once we have support for running Micro on real hardware (via the LLVM toolchain) Micro can be extended to support aliasing and memory allocations. This would be a great project for anyone that's interested in learning adding a new language feature, end to end, and extending IRs for supporting new operations.
3. Perhaps this project could be used as the starting point for creating an openly available, community maintained, compiler construction course. Something like the "[Writing an OS in Rust](https://os.phil-opp.com/)" course by Philipp Oppermann. 
