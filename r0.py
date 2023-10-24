from z3 import *
set_param(unsat_core=True)

# Helpers

predicates = {}
my_proofs = {}

def require(s, assertion):
    # black magic introspection shit
    import traceback,ast
    frame = traceback.extract_stack()[-2]
    code = frame.line
    yea = ast.parse(code)
    yea = list(ast.iter_child_nodes(next(ast.iter_child_nodes(next(ast.iter_child_nodes(yea))))))[2]
    yea = ast.unparse(yea)

    p = FreshBool()
    predicates[p] = (yea, frame.lineno, frame.name)
    s.assert_and_track(assertion, p)

def print_unsat_core(s):
    for p in s.unsat_core():
        code, lineno, name = predicates[p]
        print(f'* {str(p):5} {"line " + str(lineno):9} {name:16}  {code}')

def my_proof(s, name=None):
    def decorating_function(user_function):
        if name is None:
            assert(user_function.__name__.startswith('proof_'))
            _name = user_function.__name__[6:]
        else:
            _name = name # shadowing bullshit
        def decorated_function(*args, **kwargs):
            s.push()
            user_function(*args, **kwargs)
            # s.check()
            # print(s.assertions())
            # print(s.model())
            assert(s.check() == unsat)
            print('Unsat core:')
            print_unsat_core(s)
            s.pop()
        my_proofs[_name] = decorated_function
        return decorated_function
    return decorating_function

def run_proof(name):
    func = my_proofs[name]
    print(name)
    func()
    print('-> ok')

def run_proofs():
    for name in my_proofs:
        run_proof(name)

# Modeling

EscrowState = Datatype('EscrowStateEnum')
EscrowState.declare('OPEN')
EscrowState.declare('SUCCESS')
EscrowState.declare('REFUND')
EscrowState = EscrowState.create()
## addresses are 160bits
AddressSort = BitVecSort(160)
Address = lambda x: BitVecVal(x, AddressSort)
UintSort = BitVecSort(256)
Uint = lambda x: BitVecVal(x, UintSort)

MAX_ETH = Uint(120000000e18)
GOAL = Uint(10000e18)
# [ASSUMPTION] the instance of escrow in crowdsale use 1234e8 as eb address
ESCROW_BENEFICIARY = Address(1234e8)
# represent the address of Crodsale Contract
OWNER = BitVec("owner", AddressSort)
ENDTIME = 30

Escrow_Address = BitVec('Escrow_Address', AddressSort)

# States:
# investor_deposits :: mapping(address => uint256)
# eth_balances :: mapping(address => uint256)
# raised :: Uint
# escrowstate :: Symbolic STATE

def initial_state():
    s = Solver()

    myUser = Const('myUser', AddressSort)
    # initialDeposit = Const('initialDeposit', UintSort)
    investor_deposits = Array('investor_deposits', AddressSort, UintSort)
    eth_balances = Array('eth_balances', AddressSort, UintSort)
    # raised = Const('raised', UintSort)
    # Arbitrary escrow state
    escrowstate = Const('escrowstate', EscrowState)
    # TODO
    # - time

    # Borrow from blog post
    # reasonable constraints.
    a = Const('a', AddressSort)
    require(s, ForAll([a], ULE(investor_deposits[a], eth_balances[Escrow_Address])))
    require(s, ForAll([a], ULE(eth_balances[a], MAX_ETH)))

    # [ASSUMPTION] 
    # - ether balance of escrow and sum of all deposits is equall at the beginning
    #   , here assume both to be 0
    #   raised, eth_balance[escrow_address], all elem of deposits = 0
    # - only one depositor
    investor_deposits = Store(investor_deposits, myUser, Uint(0))
    eth_balances = Store(eth_balances, Escrow_Address, Uint(0))
    raised = eth_balances[Escrow_Address]
    
    # require(s, myUser != ESCROW_BENEFICIARY)
    # require(s, myUser != Escrow_Address)
    # require(s, ForAll([a], allowance[myUser][a] == 0))
    # starting_balance = eth_balances[myUser]

    escrow_state = (investor_deposits, escrowstate)
    state = (eth_balances, raised, escrow_state)

    # state = deposit(s, state, myUser, initialDeposit)

    return s, state, myUser


## Trans Rules

# modifier
def escrow_onlyOwner(s, msg_sender):
    # SIDE-EFFECT: add new assertion into solver
    require(s, msg_sender == OWNER) 

def escrow_close(s, state, msg_sender, msg_value):
    #onlyOwner
    escrow_onlyOwner(s, msg_sender)
    
    _, _, escrow_state = state
    _, escrowstate = escrow_state

    require(s, escrowstate == EscrowState.SUCCESS)

    return state

def escrow_refund(s, state, msg_sender, msg_value):
    #onlyOwner
    escrow_onlyOwner(s, msg_sender)

    _, _, escrow_state = state
    _, escrowstate = escrow_state
    
    require(s, escrowstate == EscrowState.REFUND)

    return state

# payable, explicit arg
def escrow_deposit(s, state, msg_sender, msg_value, p):
    # onlyOwner
    escrow_onlyOwner(s, msg_sender)

    eth_balances, raised, escrow_state = state
    inv_deposits, escrowstate = escrow_state

    # implicit from how EVM works
    require(s, UGE(eth_balances[p], msg_value))
    eth_balances = Store(eth_balances, p, eth_balances[p] - msg_value)
    eth_balances = Store(eth_balances, Escrow_Address, eth_balances[Escrow_Address] + msg_value)

    # deposits[p] = deposits[p] + msg.value;
    inv_deposits = Store(inv_deposits, p, inv_deposits[p] + msg_value)

    return (eth_balances, raised, (inv_deposits, escrowstate))

def escrow_withdraw(s, state, msg_sender, msg_value):
    eth_balances, raised, escrow_state = state
    inv_deposits, escrowstate = escrow_state

    # require(state == State.SUCCESS);
    require(s, escrowstate == EscrowState.SUCCESS)

    # beneficiary.transfer(address(this).balance);
    balance = eth_balances[Escrow_Address]
    # Always true
    require(s, UGE(balance, balance))
    eth_balances = Store(eth_balances, ESCROW_BENEFICIARY, eth_balances[ESCROW_BENEFICIARY] + balance)
    eth_balances = Store(eth_balances, Escrow_Address, balance - balance)

    return (eth_balances, raised, (inv_deposits, escrowstate))

# explicit args payable
def escrow_claimRefund(s, state, msg_sender, msg_value, p):
    eth_balances, raised, escrow_state = state
    inv_deposits, escrowstate = escrow_state

    # require(state == State.REFUND);
    require(s, escrowstate == EscrowState.REFUND)
    # uint256 amount = deposits[p];
    amount = inv_deposits[p]
    # deposits[p] = 0;
    inv_deposits = Store(inv_deposits, p, 0)
    # p.transfer(amount);
    require(s, UGE(eth_balances[Escrow_Address], amount))
    eth_balances = Store(eth_balances, p, amount)
    eth_balances = Store(eth_balances, Escrow_Address, eth_balances[Escrow_Address] - amount)

    return (eth_balances, raised, (inv_deposits, escrowstate))


# For Crowdsale contract

def invest(s, state, msg_sender, msg_value):
    eth_balances, raised, escrow_state = state
    inv_deposits, escrowstate = escrow_state

    # require(now<=closeTime)
    require(s, raised < GOAL)
    
    # escrow.deposit.value(msg.value)(msg.sender);
    eth_balances, raised, escrow_state = escrow_deposit(s, state, OWNER, msg_value, msg_sender)

    raised += msg_value

    return (eth_balances, raised, (inv_deposits, escrowstate))

def close(s, state, msg_sender, msg_value):
    _, raised, escrow_state = state
    _, escrowstate = escrow_state

    # time can be omitted(?)
    # require(now > closeTime || raised >= goal);

    # if int(str(raised)) >= int(str(GOAL)): # escrow.close();
        # state = escrow_close(s, state, msg_sender, msg_value)
    # else: # escrow.refund();
        # state = escrow_refund(s, state, msg_sender, msg_value)
    p = If(raised >= GOAL,
           escrowstate == EscrowState.SUCCESS,
           escrowstate == EscrowState.REFUND)

    require(s, p)

    return state

## External call to TRs
## - Wrap the TRs around abstraction to symbolize the params
## - Computation with onlyOwner modifier can be temporary ignored

def symbolic_invest(s, state, myUser):
    user = myUser
    value = FreshConst(UintSort, 'value')
    
    # arbitary user except Escrow and Crowdsale
    require(s, user != Escrow_Address)
    require(s, user != OWNER)
    
    state = invest(s, state, user, value)

    return state

def symbolic_close(s, state, myUser):
    user = myUser
    value = FreshConst(UintSort, 'value')
    
    # arbitary user except Escrow and Crowdsale
    require(s, user != Escrow_Address)
    require(s, user != OWNER)
    
    state = close(s, state, user, value)

    return state

def symbolic_escrow_withdraw(s, state, myUser):
    user = myUser
    value = FreshConst(UintSort, 'value')
    
    require(s, user != Escrow_Address)
    require(s, user != OWNER)
    
    state = escrow_withdraw(s, state, user, value)

    return state

def symbolic_escrow_claimRefund(s, state, myUser):
    user = myUser
    value = FreshConst(UintSort, 'value')
    
    require(s, user != Escrow_Address)
    require(s, user != OWNER)
    
    state = escrow_claimRefund(s, state, user, value, user)

    return state

def is_ok_r0(state, myUser):
    # TODO
    # is_ok_r0 :: (...) -> predicates
    # @predicate: property to be settled
    # p = TODO
    # new_state = withdraw(s2, state, myUser, initialDeposit)
    eth_balances, raised, escrow_state = state
    inv_deposits, escrowstate = escrow_state
    
    # p = If(escrowstate != EscrowState.SUCCESS, 
        #    inv_deposits[myUser] == eth_balances[Escrow_Address], 
        #    True)

    p = If(escrowstate != EscrowState.SUCCESS, 
           raised == eth_balances[Escrow_Address], 
           True)

    return p

# --- Proving ---
# Yet another expression problem
# - r0: The sum of all investor deposits equals the ether balance
#       of the escrow unless the crowdsale is declared successful

s, state, myUser = initial_state()

def sanity_check(cur_state, myUser):
    # sanity check. Let's make sure the initial state is valid
    s.push()
    s.add(Not(is_ok_r0(cur_state, myUser)))
    # print(s.assertions())
    # assert(s.check() == unsat)
    s.pop()

sanity_check(state, myUser)

def test(s, state):
    pass

print("BMC Inductive Proof of property r0|r1")

@my_proof(s)
def proof_invest():
    new_state = symbolic_invest(s, state, myUser)
    require(s, Not(is_ok_r0(new_state, myUser)))

@my_proof(s)
def proof_escrow_withdraw():
    new_state = symbolic_escrow_withdraw(s, state, myUser)
    require(s, Not(is_ok_r0(new_state, myUser)))
    # print(s.assertions())

@my_proof(s)
def proof_escrow_claimRefund():
    new_state = symbolic_escrow_claimRefund(s, state, myUser)
    require(s, Not(is_ok_r0(new_state, myUser)))
    # print(s.assertions())

@my_proof(s)
def proof_close():
    new_state = symbolic_close(s, state, myUser)
    require(s, Not(is_ok_r0(new_state, myUser)))
    # print(s.assertions())

run_proofs()