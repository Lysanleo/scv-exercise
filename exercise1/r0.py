from z3 import *
set_param(unsat_core=True)

# Helpers

my_proofs = {}

def require(s, assertion):
    # TODO
    # require :: solver -> assertion -> SideEffect
    # SIDE-EFFECT:
    # - assert and track assertion in solver
    pass

def my_proof(s, name=None):
    def decorating_function(user_function):
        if name is None:
            assert(user_function.__name__.startswith('proof_'))
            _name = user_function.__name__[6:]
        else:
            _name = name
        def decorated_function(*args, **kwargs):
            # solver scope
            s.push()
            user_function(*args,**kwargs)
            # unsatisfiably of NOT(is_ok(p)) => proof of is_ok(p)
            assert(s.check() == unsat)
            # print("Unsat core:")
            # print_unsat_core(s)
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

## addresses are 160-bit
EscrowState = Datatype('EscrowStateEnum')
EscrowState.declare('OPEN')
EscrowState.declare('SUCCESS')
EscrowState.declare('REFUND')
EscrowState = EscrowState.create()
AddressSort = BitVecSort(160)
Address = lambda x: BitVecVal(x, AddressSort)
UintSort    = BitVecSort(256)
Uint = lambda x: BitVecVal(x, UintSort)

WETH_Address = BitVec('WETH_Address', AddressSort)
MAX_ETH = Uint(120000000e18)
# [ASSUMPTION] the instance of escrow in crowdsale use 1234e10 as eb address
ESCROW_BENEFICIARY = Address(1234e8)
Escrow_Address = BitVec('Escrow_Address', AddressSort)
GOAL = Uint(10000e18)
OWNER = BitVec("owner", AddressSort)

# States
# investor_deposits :: mapping(address => uint256)
# eth_balances :: mapping(address => uint256)

def initial_state():
    s = Solver()

    myUser = Const('myUser', AddressSort)
    initialDeposit = Const('initialDeposit', UintSort)
    investor_deposits = Array('investor_deposits', AddressSort, UintSort)
    eth_balances = Array('eth_balances', AddressSort, UintSort)
    raised = Uint(0)
    escrowstate = Const('escrowstate', EscrowState)
    #TODO
    # - time
    # - invest states
    # - 

    # Borrow from blog post
    # manually defined constraint.
    a = Const('a', AddressSort)
    require(s, ForAll([a], ULE(investor_deposits[a], eth_balances[ESCROW_BENEFICIARY])))
    require(s, ForAll([a], ULE(eth_balances[a], MAX_ETH)))

    # [ASSUMPTION] 
    investor_deposits = Store(investor_deposits, myUser, Uint(0))
    # require(s, myUser != ESCROW_BENEFICIARY)
    require(s, myUser != Escrow_Address)
    # require(s, ForAll([a], allowance[myUser][a] == 0))
    starting_balance = eth_balances[myUser]

    escrow_state = (investor_deposits, escrowstate)
    state = (eth_balances, raised, escrow_state)

    #TODO
    # state = deposit(s, state, myUser, initialDeposit)

    return s, state, myUser, initialDeposit, starting_balance



## Trans Rules

### For escrow_deposit
# - TODO How to modeling constructor?

# modifier
# SIDE-EFFECT :: add new assertion into solver
def escrow_onlyOwner(s, msg_sender):
    require(s, msg_sender == OWNER) 

def escrow_close(s, state, msg_sender, msg_value):
    escrow_onlyOwner(s, msg_sender)
    
    eth_balances, raised, escrow_state = state
    inv_deposits, escrowstate = escrow_state

    escrow_state = EscrowState.SUCCESS

    return (eth_balances, raised, (inv_deposits, escrowstate))

def escrow_refund(s, state, msg_sender, msg_value):
    escrow_onlyOwner(s, msg_sender)

    eth_balances, raised, escrow_state = state
    inv_deposits, escrowstate = escrow_state
    
    escrow_state = EscrowState.REFUND

    return (eth_balances, raised, (inv_deposits, escrowstate))

# payable, explicit arg
def escrow_deposit(s, state, msg_sender, msg_value, p):
    # onlyOwner modifier
    escrow_onlyOwner(s, msg_sender)

    eth_balances, raised, escrow_state = state
    inv_deposits, escrowstate = escrow_state

    # implicit from how EVM works
    require(s, UGE(eth_balances[msg_sender], msg_value))
    eth_balances = Store(eth_balances, msg_sender, eth_balances[msg_sender] - msg_value)
    eth_balances = Store(eth_balances, Escrow_Address, eth_balances[WETH_Address] + msg_value)

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
    require(s, escrowstate, EscrowState.REFUND)
    # uint256 amount = deposits[p];
    # TODO fix
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
    pass

def close(s, state, msg_sender, msg_value):
    pass

## External call to TRs
## - Wrap the TRs around abstraction to symbolize the params

## other

def is_ok_r0(s, state, myUser, initial):
    # TODO
    # is_ok_r0 :: (...) -> predicates
    # @predicate: property to be settled
    # p = Or(sum of deposits == eth_balance of excrow
    #       ,escrow_state == success)
    pass


# --- Proving ---
# Yet another expression problem
# - r0: The sum of all investor deposits equals the ether balance
#       of the escrow unless the crowdsale is declared successful
#   equal with
#   r0'(?): raised equals the ether balance
#           of the escrow after invest
# TODO Begin with initial state


def sanity_check(cur_state):
    # Make sure the initial state is valid
    s.push()
    # s.add(Not(is_ok(s, cur_state)))
    assert(s.check() == unsat)
    s.pop()

sanity_check(state)

@my_proof(s)
def proof_():
    pass 

run_proofs()