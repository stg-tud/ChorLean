# ChorLean

Implementation of choreographic library based programming in the style of HasChor/MultiChor

## Usage

### Roles

First, a Choreo requires an instance of the *Role* class.
*Role* specifies how many entities participate in the choreography and gives them unique string identifiers.
These identifiers are used for debugging information, and to select which role to execute when running choreographies on the command line.
Optionally, the *adj* (adjacency) field can specify which roles are allowed to communicate with which other role. 
By default, there are no restrictions on adjacency between roles.

#### Buyer-Seller Roles

Here is an example Role instance taken from the bookseller example:
```lean
instance: Role where
  N := 2
  name | 0 => "buyer" | 1 => "seller"
```

### Executing Endpoint
Choreographic code is always executed by a single role that runs those instructions relevant to them.
This role is an argument for running choreographies, and usually passed by the user when starting the program on the command line.
Programmers do not have direct access to the endpoint, but only through the RID (RoleIDEntity) class.
The RID class contains a role (RID.id) and evidence that this role is in fact the currently executing one (RID.is_ep).
*rid* is an abbreviation for RID.id

### Choreo Monad

Choreographies in ChorLean are written in the *Choreo* Monad.
*Choreo* is parameterized by:
- the List of roles that participate in that function (present roles). All other roles will ignore that code. 
- Evidence that the endpoint is member of this list.

### Main Entrypoint
Chorlean provides a function that automatically generates the main function for you, called *CHOR_ENTRYPOINT*, and a main function is expected to be defined as:
```lean
def main := CHOR_ENTRYPOINT
```
CHOR_ENTRYPOINT lets you run the choreography by running the Lean program and supplying the *Role.name* as the first command line argument.
CHOR_ENTRYPOINT expects an instance of the *ChorMain* class, containing the actual Main method.
The Main method maps the command line inputs as a faceted list of strings, to a choreography that initially contains *all* roles.

### Located Values and Types

Types in ChorLean are annotated a list of roles that knowledge of their underlying value.
They are notated as *α @ p* where *α* is a type and *p* a predicate over roles.
Located values are defined as functions from evidence, that the executing role has knowledge of the value (is member of the list), to the value itself. Such evidence can be gathered by *enclaving*.
Helpful functions around located values include:

- Located.wrap: wraps values into located values
- Located.flatten: removes one layer of nested located values
- Located.cast: casts into a located value with different list of owners *p'*, if *p ⊆  p'*. This is helpful when two lists contain the same set of roles but are not equal, like *[A]* and *[A,A]*
- Located.un: unwraps a located value. Requires an instance of RID and the executing role to be member of the owners. This member proof is tried to be inferred automatically but sometimes has to be entered manually 

#### Faceted
Maps roles to located values which are located at them. Helpful for parallel computations.

### Basic Operations

The Core of ChorLean is built on only 3 functions

1. Enclave: embeds a choreography containing less present roles into a bigger one.
2. Broadcast: broadcasts a located value to all present roles, such that it can then be used as a non-located value.
3. Locally: runs a program on the present role. *Requires* a single location to be present. IO Programs are automatically lifted into the choreography with an RID instance.
### Other helpful functions and notations:

#### Enclaves

The examples make use the following notation for enclave: *a ~~ b* and *a °° b*, where *a* is a list of roles, being a subset of the currently present ones, and *b* is the subchoreography to enclave. By using the *°°*, the result of the enclave is also broadcasted. By *[A]° IO.getLine* the Role A would perform a getline program locally and broadcast it afterwards.
There are alternative notations if only a single role is enclaved with only a single symbol *a ~ b* and *a ° b*. These versions provide an RID class instance to the user with access to the currently executing role.

#### Parallel

Iterates over all present roles to perform a program locally on them. The program in this case has knowledge of the identity of the executing role by an RID instance. Results in *faceted* values. A Choreography where every role prints their identity might look like this
```lean
par (IO.println s!"hello from {Role.name rid}")
```

#### Scatter/Gather

A sender can scatter data located at him by sending every present role a value of the same type, resulting in a faceted value. To inverse this, a faceted value can be gathered in a single location again.
Additionally, there is a *scatterList* and *gatherList* variant, which scatters and gathers list items evenly. *gatherAll* is a variant of gather that gathers results replicated at all roles, not just a single one.

## Examples
run the examples by:
```
booseller:
lake exe books buyer
lake exe books seller

authentication:
lake exe auth client
lake exe auth service
lake exe auth IP

mergesort:
lake exe merge master
lake exe merge W1
lake exe merge W2
```