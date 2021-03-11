#include <eosio/transaction.hpp>
#include <eosio/crypto.hpp>
#include <eosio/asset.hpp>
#include <eosio/eosio.hpp>
#include <eosio/system.hpp>

using namespace std;
using namespace eosio;

constexpr uint8_t CHAIN_ID[32] =  {0xac,0xa3,0x76,0xf2,0x06,0xb8,0xfc,0x25,
                                   0xa6,0xed,0x44,0xdb,0xdc,0x66,0x54,0x7c,
                                   0x36,0xc6,0xc3,0x3e,0x3a,0x11,0x9f,0xfb,
                                   0xea,0xef,0x94,0x36,0x42,0xf0,0xe9,0x06}; // Mainnet chain ID

constexpr auto FEE_ACCOUNT         = "eosfinexfees"_n;
constexpr auto EVENT_NAME          = "eosfinexevnt"_n;
constexpr auto EXCH_PRECISION      = 8;
constexpr auto EXCH_SERVICE_DELAY  = 60 * 60 * 24; // Exchange has 24 hours to service withdraw before customer can force it

class [[eosio::contract]] eosfinex : public contract {

  // Used only to examine eosio.token contracts

  struct [[eosio::table]] currency_stats {
     asset    supply;
     asset    max_supply;
     name     issuer;

     uint64_t primary_key()const { return supply.symbol.code().raw(); }
  };
  typedef eosio::multi_index< "stat"_n, currency_stats > stats;

  // Start local table storage structs

  struct [[eosio::table]] ste {
    uint32_t     id = 0;
    uint64_t  reserved1;

    uint64_t primary_key() const noexcept { return 0; }
  };
  typedef eosio::multi_index< "state"_n, ste> state;

  struct [[eosio::table]] listedtoken {
    symbol   token;
    name     issuer;
    uint64_t minsize;
    uint64_t  reserved1;

    uint64_t primary_key() const { return token.code().raw(); }
  };
  typedef eosio::multi_index<"listedtokens"_n, listedtoken> listedtokens;

  struct [[eosio::table]] usr {
    public_key pubkey;
    uint64_t  status;
    uint64_t  reserved1;

    uint64_t primary_key() const noexcept { return 0; }

    EOSLIB_SERIALIZE( usr, (pubkey)(status)(reserved1) )
  };
  typedef eosio::multi_index< "users"_n, usr> users;

  struct [[eosio::table]] account {
    asset  balance;
    uint64_t  reserved1;

    uint64_t primary_key() const noexcept { return balance.symbol.code().raw(); }
  };
  typedef eosio::multi_index< "accounts"_n, account> accounts;

  struct [[eosio::table]] request {
    asset    quantity;
    uint32_t time;
    uint64_t  reserved1;

    uint64_t primary_key() const noexcept { return quantity.symbol.code().raw(); }
  };
  typedef eosio::multi_index< "requests"_n, request> requests;

  struct [[eosio::table]] fill {
    uint64_t id;
    checksum256 hash;
    uint64_t filled;
    uint32_t expiration;
    uint64_t  reserved1;

    uint64_t primary_key() const noexcept { return id; }
    checksum256 get_secondary() const noexcept { return hash; }
    uint64_t get_expiration_index() const noexcept { return expiration; }
  };
  typedef eosio::multi_index<"fills"_n, fill
       ,indexed_by< "hash"_n,
           const_mem_fun<fill, checksum256, &fill::get_secondary>
       >
       ,indexed_by< "expiration"_n,
           const_mem_fun<fill, uint64_t, &fill::get_expiration_index>
       >
   > fills;

public:

  // Start types

  struct Order {
    uint32_t    seskey1;
    uint32_t    seskey2;
    uint64_t    nonce;
    asset       price;
    asset       amount;
    uint64_t    flags;

    inline bool isBuy()              const noexcept { return amount.amount > 0; }

    inline bool isMarketOrder()      const noexcept { return flags & 0b00000001; }
    inline bool isReleaseOnTrade()   const noexcept { return flags & 0b00000010; }
  };

  struct SignedTransaction : public transaction {
    vector<signature> signatures;
    vector<uint8_t>   context_free_data;
  };

  enum WalletUpdateReason {
    Deposit = 0,
    Withdraw = 1,
    Trade = 2
  };

private:

  // Start helper functions

  inline uint32_t now() const noexcept {
      return eosio::current_time_point().sec_since_epoch();
  }

  inline void releaseOnTrade(const name account, const asset& quantity, const name issuer) noexcept {

     transaction t{};
     t.actions.emplace_back(
         eosio::permission_level{get_self(), "active"_n},
         issuer,
         "transfer"_n,
         std::make_tuple(get_self(),account,quantity,std::string("Release on trade")));
     t.delay_sec = 0;
     t.send(nextUniqueId(), get_self());
  }

  uint64_t nextUniqueId() noexcept {
    uint32_t id;
    auto uniqueIdLambda = [&]( auto& obj ) {
      id = ++obj.id;
    };
    state statetbl( get_self(), get_self().value );
    auto state = statetbl.begin();
    if ( state == statetbl.end() ) {
      statetbl.emplace( get_self(), uniqueIdLambda);
    } else {
      statetbl.modify( state, eosio::same_payer, uniqueIdLambda);
    }

    return id;
  }

  const listedtoken getToken( const symbol_code code ) const noexcept {
    listedtokens listedtokenstbl( get_self(), get_self().value );
    auto token = listedtokenstbl.find( code.raw() );
    check( token != listedtokenstbl.end(), "Unknown token" );

    return *token;
  }

  const usr getUser( const name account ) const noexcept {
    users usertbl( get_self(), account.value );
    auto user = usertbl.begin();
    check( user != usertbl.end(), "Unknown user" );

    return *user;
  }

  asset getBalance(const name owner, const symbol& sym) const noexcept {
    accounts accountstbl( get_self(), owner.value );
    auto from = accountstbl.find( sym.code().raw() );
    return normalizedAsset( from != accountstbl.end() ? from->balance.amount : 0, EXCH_PRECISION, sym);
  }

  void subBalance(const name owner, const asset& value, const WalletUpdateReason reason) noexcept {
    auto balance = value;

    check( value.amount >= 0, "Negative value not allowed" );

    accounts accountstbl( get_self(), owner.value );
    auto from = accountstbl.find( value.symbol.code().raw() );
    check( from != accountstbl.end() && from->balance >= value, "Overdrawn balance"
       " for account " + owner.to_string() + " " + value.to_string() );

    if (from->balance == value) {
      accountstbl.erase( from );
      balance.amount = 0;
    } else {
      accountstbl.modify( *from, eosio::same_payer, [&]( auto& a ) {
        balance = a.balance -= value;
      });
    }

    print("value: ", value, ", balance: ", balance);

    action{
      eosio::permission_level{get_self(), "active"_n},
      EVENT_NAME,
      "wallet"_n,
      std::make_tuple(owner,-value, balance, uint8_t(reason))
    }.send();
  }

  void addBalance(const name owner, const asset& value, const WalletUpdateReason reason) noexcept {
    auto balance = value;

    check( value.amount >= 0, "Negative value not allowed" );
    accounts accountstbl( get_self(), owner.value );
    auto to = accountstbl.find( value.symbol.code().raw() );
    if (to == accountstbl.end()) {
      accountstbl.emplace( get_self(), [&]( auto& a ) {
        a.balance = value;
      });
    } else {
      accountstbl.modify( to, eosio::same_payer, [&]( auto& a ) {
        balance = a.balance += value;
      });
    }

    print("value: ", value, ", balance: ", balance);

    action{
      eosio::permission_level{get_self(), "active"_n},
      EVENT_NAME,
      "wallet"_n,
      std::make_tuple(owner, value, balance, uint8_t(reason))
    }.send();
  }

  bool isValidQty(const checksum256& hash, const uint64_t tradeAmount, const int64_t orderAmount, const time_point_sec orderExpiration) noexcept {

    // All quantities here are represented with EXCH_PRECISION
    //  digits of precision to the right of the decimal

    fills fillstbl( get_self(), get_self().value );
    auto myindex = fillstbl.get_index<name("hash")>();

    auto fill = myindex.find( hash );
    if ( fill != myindex.end() )  {
      if ( fill->filled + tradeAmount > llabs( orderAmount ) ) return false;
      check( fill->expiration == orderExpiration.utc_seconds, "Order expiration must match existing fill expiration" );
      myindex.modify( fill, eosio::same_payer, [&]( auto& a ) {
        a.filled += tradeAmount;
      });
    } else {
      if ( tradeAmount > llabs( orderAmount ) ) return false;
      fillstbl.emplace( get_self(), [&]( auto& a ) {
        a.id = fillstbl.available_primary_key();
        a.hash = hash;
        a.filled = tradeAmount;
        a.expiration = orderExpiration.utc_seconds;
      });
    }

    return true;
  }

  asset normalizedAsset(uint128_t norm, const uint8_t fromPrecision, const symbol& toSymbol) const noexcept {
    for ( auto p = fromPrecision; p > toSymbol.precision(); --p, norm /= 10 );
    for ( auto p = fromPrecision; p < toSymbol.precision(); ++p, norm *= 10 );
    check( norm <= asset::max_amount, "Error normalizing value: overflow" );
    return asset{ static_cast<int64_t>(norm), toSymbol };
  }

  checksum256 getTransactionHash( const SignedTransaction& order ) const noexcept {

    const auto DATA_BUFFER_SIZE = 256;  // Ensure we have enough room to write the signature part of the signed trans even if overwritten
    const auto PACKED_TRANS_SIZE = 50;  // Magic number - this is the base size of a packed transaction without any data
    char data[DATA_BUFFER_SIZE];

    //Copy chain id into buffer
    memcpy( data, CHAIN_ID, sizeof(CHAIN_ID) );

    // Serialize transaction into buffer
    datastream ds1( data + sizeof(CHAIN_ID), DATA_BUFFER_SIZE - sizeof(CHAIN_ID) );
    ds1 << order;

    // Set cfd hash in buffer to all zeros
    memset( data + sizeof(CHAIN_ID) + PACKED_TRANS_SIZE + sizeof(Order), 0, sizeof(checksum256) );

    // Return hash of buffer
    return sha256( data, sizeof(CHAIN_ID) + PACKED_TRANS_SIZE + sizeof(Order) + sizeof(checksum256) );
  }

  tuple<const Order&, const name, const checksum256>
  verifyTransactionAndReturnDetails( const SignedTransaction& trans, const std::string side ) const noexcept {

    // Check transaction details
    const auto time = now();
    check( time < trans.expiration.utc_seconds, "Signed " + side + " transaction has expired" );
    check( trans.context_free_actions.size() == 0, "Singed " + side + " transaction cannot have context free actions" );
    check( trans.transaction_extensions.size() == 0, "Signed " + side + " transaction cannot have transaction extensions" );
    check( trans.signatures.size() == 1, "Signed " + side + " transaction can have only one sigature" );
    check( trans.context_free_data.size() == 0, "Signed " + side + " transaction cannot have any context free data" );

    // Check basic action details
    check( trans.actions.size() == 1, "Signed " + side + " transaction can only have one action" );
    const auto& act = trans.actions[0];
    check( act.account == get_self(), "Signed " + side + " transaction's place action must reference this account" );
    check( act.name == "place"_n, "Signed " + side + " transaction must contain the 'place' action" );
    check( act.authorization.size() == 1, "Signed " + side + " transaction's place action must have only one authorization" );
    check( act.data.size() == sizeof(Order), "Incorrect size for signed " + side + " transaction's place action" );

    // Get user account from transaction
    const auto account = act.authorization[0].actor;
    const auto user = getUser( account );

    check( user.status & 0x1 ,"Signed " + side + " transaction user status is not active" );

    // Hash order and compare keys
    const auto hash = getTransactionHash( trans );
    check( recover_key( hash, trans.signatures[0] ) == user.pubkey, "Signed " + side + " transaction signature is invalid for user's registered public key" );

    return { *reinterpret_cast<const Order*>(&act.data[0]), account, hash };
  }

  public:
    using contract::contract;

    // Start actions

    [[eosio::action]]
    void place( const Order& order ) {} // ABI can be used by clients to generate signed transactions

    [[eosio::on_notify("*::transfer")]]
    void ontransfer( const name from, const name to, const asset quantity, const string memo ) {

      const auto token = getToken( quantity.symbol.code() );
      check( token.issuer == get_first_receiver(), "Can only accept transfers of white listed tokens" );
      check( quantity.symbol.precision() == token.token.precision(), "Unsupported asset precision" );

      // Redundant checks
      check( from != to, "Cannot transfer to self" );
      check( quantity.is_valid(), "Invalid asset" );
      check( quantity.amount > 0, "Amount must be >= 0" );
      // Redundant checks
      
      const auto normQuantity = normalizedAsset( quantity.amount, quantity.symbol.precision(), symbol(quantity.symbol.code(),EXCH_PRECISION) );
      if ( from == get_self() ) {

        check( to != "eosio.ram"_n && to != "eosio.ramfee"_n && to != "eosio.stake"_n,
            "Must buy RAM or stake for contract from another account" );

        require_auth( get_self() ); // Extra security - token contract should already check
        subBalance( to, normQuantity, WalletUpdateReason::Withdraw );
      } else { 

        check( to == get_self(), "Contract must be eosfinexeos1" );
        check( quantity.amount >= token.minsize, "Transfer is less than the minimum required quantity" );

        const auto user = getUser( from ); // Will assert if user does not have an account
        check( user.status & 0x1, "User status must be active in order to deposit funds" );
        addBalance( from, normQuantity, WalletUpdateReason::Deposit );
      }
    }

    [[eosio::action]]
    void reguser( const name account, const public_key& pubkey, const uint32_t tos ) {

      require_auth( account );
      require_auth( get_self() );

      users usertbl( get_self(), account.value );
      auto user = usertbl.begin();
      check( user == usertbl.end(), "User already registered" );

      usertbl.emplace( get_self(), [&]( auto& a ) {
        a.pubkey = pubkey;
        // tos is upper 32 bits and status is lower 32 bits
        a.status = ( uint64_t( tos ) << 32 ) | 1;
      });
    }

    [[eosio::action]]
    void userkey( const name account, const public_key& pubkey ) {

      require_auth( account );
      require_auth( get_self() );

      users usertbl( get_self(), account.value );
      auto user = usertbl.begin();
      check( user != usertbl.end(), "User must be registered" );

      usertbl.modify( user, eosio::same_payer, [&]( auto& a ) {
        a.pubkey = pubkey;
      });
    }

    [[eosio::action]]
    void usertos( const name account, const uint32_t tos ) {

      require_auth( account );

      users usertbl( get_self(), account.value );
      auto user = usertbl.begin();
      check( user != usertbl.end(), "User must be registered" );

      usertbl.modify( user, eosio::same_payer, [&]( auto& a ) {
        // tos is upper 32 bits and status is lower 32 bits
        a.status = ( uint64_t( tos ) << 32 ) | ( 0xFFFFFFFF & a.status );
      });
    }

    [[eosio::action]]
    void userstatus( const name account, const uint32_t status ) {

      require_auth( get_self() );

      users usertbl( get_self(), account.value );
      auto user = usertbl.begin();
      check( user != usertbl.end(), "Account does not exist" );

      usertbl.modify( user, eosio::same_payer, [&]( auto& a ) {
        // tos is upper 32 bits and status is lower 32 bits
        a.status = ( 0xFFFFFFFF00000000 & a.status ) | status;
      });
    }

    [[eosio::action]]
     void regtoken( const name account, const symbol_code token, int64_t minsize ) {

      require_auth( get_self() );

      check( minsize >= 0, "Minsize must be >= 0" );
      check( is_account(account), "Issuer account does not exist" );

      stats statstbl( account, token.raw() );
      auto existing = statstbl.find( token.raw() );
      check( existing != statstbl.end(), "Issuer contract does not support that token" );
      auto sym = existing->supply.symbol;
      check( sym.precision() <= 9, "Contract does not support tokens with more than 9 digits of precission" );

      auto whitelistLambda = [&]( auto& obj ) {
        obj.token = sym;
        obj.issuer = account;
        obj.minsize = minsize;
      };

      listedtokens listedtokenstbl( get_self(), get_self().value );
      auto tkn = listedtokenstbl.find( token.raw() );
      if ( tkn == listedtokenstbl.end() ) {
        listedtokenstbl.emplace( get_self(), whitelistLambda );
      } else {
        check(tkn->token == sym, "Precision mismatch");
        listedtokenstbl.modify( tkn, eosio::same_payer, whitelistLambda );
      }
    }

    [[eosio::action]]
    void validate( const name account ) {
      require_auth( account );
    }

    [[eosio::action]]
    void withdraw( const name account, const asset& quantity ) {

      check( has_auth( account ) || has_auth( get_self() ), "Missing required authority" );

      const auto token = getToken( quantity.symbol.code() );
      check( quantity.symbol.precision() == token.token.precision(), "Unsupported asset precision" );

      auto balance = getBalance( account, quantity.symbol );

      requests requeststbl( get_self(), account.value );
      auto req = requeststbl.find( quantity.symbol.code().raw() );
      if (req == requeststbl.end()) {
        check( quantity.amount > 0, "Must withdraw a positive amount" );
        check( quantity <= balance, "Insufficient balance for withdraw request" );
        requeststbl.emplace( get_self(), [&]( auto& a ) {
          balance = a.quantity = quantity;
          a.time = now();
        });
      } else {
        if ( quantity.amount ) {
          check( quantity.amount > 0, "Must withdraw a positive amount" );
          check( quantity + req->quantity <= balance, "Insufficient balance for withdraw request" );
          requeststbl.modify( req, eosio::same_payer,  [&]( auto& a ) {
            balance = (a.quantity += quantity);
            a.time = now();
          });
        } else {
          requeststbl.erase( req );
        }
      }

      action{
        eosio::permission_level{get_self(), "active"_n},
        EVENT_NAME,
        "request"_n,
        std::make_tuple(account,quantity,balance)
      }.send();
    }

    [[eosio::action]]
    void srvcwithdraw( const name account, const asset& quantity ) {

      check( quantity.amount >= 0, "Must service with a non-negative amount" );

      requests requeststbl( get_self(), account.value );
      auto req = requeststbl.find( quantity.symbol.code().raw() );
      check( req != requeststbl.end(), "No pending withdraw request" );

      if ( now() < req->time + EXCH_SERVICE_DELAY ) {
        // Exchange must service withdraw request
        require_auth( get_self() );
      } else {
        // Client may also service/force withdraw request
        check( has_auth( get_self() ) || has_auth( account ), "Missing required authority" );
      }

      // Ensure quantity is correct
      const auto balance = getBalance( account, req->quantity.symbol );
      asset fullQuantity{ std::min( req->quantity.amount, balance.amount ), balance.symbol };
      check( quantity.symbol == fullQuantity.symbol, "Incorrect quantity: Symbol must match request" );
      check( quantity.amount <= fullQuantity.amount, "Incorrect quantity: Amount must be <= min of request and wallet balance" );
      
      if ( quantity.amount == fullQuantity.amount) {
        // Remove if fully serviced
        requeststbl.erase( req );
      } else {
        requeststbl.modify( req, eosio::same_payer, [&]( auto& a ) {
          a.quantity -= quantity;
        });
      }

      action{
        eosio::permission_level{get_self(), "active"_n},
        EVENT_NAME,
        "request"_n,
        std::make_tuple(account,asset{0,quantity.symbol},balance)
      }.send();

      const auto token = getToken( quantity.symbol.code() );
      if ( quantity.amount ) {
        action{
          eosio::permission_level{get_self(), "active"_n},
          token.issuer,
          "transfer"_n,
          std::make_tuple(get_self(),account,quantity,std::string("Withdraw request"))
        }.send();
      }
    }

    [[eosio::action]]
     void settle(  const uint64_t tradeId, const uint64_t buyOrderId, const uint64_t sellOrderId,
         const asset price, const asset amount, const int8_t buyFeeBps, const int8_t sellFeeBps,
         const SignedTransaction& buyTransaction, const SignedTransaction& sellTransaction ) {

      require_auth( get_self() );

      // Verify transactions
      auto [buyOrder,  buyAccount,  buyId]  = verifyTransactionAndReturnDetails( buyTransaction,  "buy" );
      auto [sellOrder, sellAccount, sellId] = verifyTransactionAndReturnDetails( sellTransaction, "sell" );

      // Basic order checks
      check( price.amount > 0, "Settlement price must be positive" );
      check( amount.amount > 0, "Settlement amount must be positive" );
      check( price.symbol.precision() == EXCH_PRECISION, "Trade price must use exchange precision" );
      check( amount.symbol.precision() == EXCH_PRECISION, "Trade amount must use exchange precision" );
      check( buyFeeBps >= 0 && sellFeeBps >= 0, "Buy and sell fees must both be non-negative" );
      check( buyFeeBps <= 50 && sellFeeBps <= 50, "Buy and sell fees must both be less than 50 bps" );
      check( buyOrder.amount.amount  &&  buyOrder.isBuy(),  "Buy order must have positive amount" );
      check( sellOrder.amount.amount && !sellOrder.isBuy(), "Sell order must have negative amount" );
      check( amount.symbol == buyOrder.amount.symbol && price.symbol == buyOrder.price.symbol, "Buy order price/amount symbols must match trade price/amount symbols" );
      check( amount.symbol == sellOrder.amount.symbol && price.symbol == sellOrder.price.symbol, "Sell order price/amount symbols must match trade price/amount symbols" );
      check( sellOrder.isMarketOrder() || sellOrder.price <= price, "Trade price would violate sell order price" );
      check( buyOrder.isMarketOrder() ||  price <= buyOrder.price,  "Trade price would violate buy order price" );

      // Check order quantities
      check( isValidQty( buyId,  amount.amount, buyOrder.amount.amount,  buyTransaction.expiration ),  "Trade quantity would violate buy order quantity" );
      check( isValidQty( sellId, amount.amount, sellOrder.amount.amount, sellTransaction.expiration ), "Trade quantity would violate sell order quantity" );

      // Normalize trade quantity
      const auto baseToken = getToken( amount.symbol.code() );
      const auto tradeQty = amount;
      const auto buyFee = tradeQty * buyFeeBps / 10000;
      const auto tradeQtyRec = tradeQty - buyFee;
      check( tradeQty == buyFee + tradeQtyRec, "Something has gone terribly wrong with amount math" );

      // Normalize trade value
      const auto quoteToken = getToken( price.symbol.code() );
      const auto tradeValue = normalizedAsset( uint128_t( amount.amount ) * price.amount, 2 * EXCH_PRECISION, symbol(price.symbol.code(), EXCH_PRECISION));
      const auto sellFee = tradeValue * sellFeeBps / 10000;
      const auto tradeValueRec = tradeValue - sellFee;
      check( tradeValue == sellFee + tradeValueRec, "Something has gone terribly wrong with value math" );

      print( "tradeQty: ", tradeQty, ", tradeValue: ", tradeValue, " | buyFee: ", buyFee, ", sellFee: ", sellFee, "\n" );

      // Update buyer balances
      addBalance( buyAccount, tradeQtyRec, WalletUpdateReason::Trade );
      subBalance( buyAccount, tradeValue, WalletUpdateReason::Trade );

      // Update seller balances
      subBalance( sellAccount, tradeQty, WalletUpdateReason::Trade );
      addBalance( sellAccount, tradeValueRec, WalletUpdateReason::Trade );

      // Update exchange balances
      if ( buyFee.amount )  addBalance( FEE_ACCOUNT, buyFee, WalletUpdateReason::Trade );
      if ( sellFee.amount ) addBalance( FEE_ACCOUNT, sellFee, WalletUpdateReason::Trade );

      // TODO: We must think more about eosfinex gateway race condition before supporting release on trade
      //if ( buyOrder.isReleaseOnTrade() ) {
      //  releaseOnTrade( buyAccount, tradeQty, baseToken.issuer );
      //}
      //if ( sellOrder.isReleaseOnTrade() ) {
      //  releaseOnTrade( sellAccount, tradeValue, quoteToken.issuer );
      //}

      // Send an event to make life easier for the eosfinex gateway
      action{
        eosio::permission_level{get_self(), "active"_n},
        EVENT_NAME,
        "trade"_n,
        std::make_tuple(tradeId)
      }.send();
    }

    [[eosio::action]]
    void prune( const uint32_t size ) {
      check( size, "Size must be greater than zero" );

      fills fillTable( get_self(), get_self().value );
      auto myindex = fillTable.get_index<name("expiration")>();

      auto time = now();
      int i = 0;
      for (auto fill = myindex.begin(); i < size && fill != myindex.end(); ++i, fill = myindex.begin()) {
        if ( fill->expiration > time ) {
          break;
        }

        myindex.erase( fill );
      }

      check( i, "No fills to prune" );
      print( "Pruned ", i, " fills\n" );
    }

    [[eosio::action]]
    void cancel( const SignedTransaction& signedTransaction ) {

      require_auth( get_self() );

      auto [o,  orderAccount,  id]  = verifyTransactionAndReturnDetails( signedTransaction,  "order" );

      require_auth( orderAccount );

      // Grab references so we can capture in the lambda
      const auto& order = o;
      const auto& orderId = id;

      fills fillstbl( get_self(), get_self().value );
      auto myindex = fillstbl.get_index<name("hash")>();

      auto fill = myindex.find( orderId );
      if ( fill != myindex.end() )  {
        check( fill->filled < llabs( order.amount.amount ), "Order is already marked as fully filled" );
        check( fill->expiration == signedTransaction.expiration.utc_seconds, "Order expiration must match existing fill expiration" );
        myindex.modify( fill, orderAccount, [&]( auto& a ) {
          a.filled = order.amount.amount;
        });
      } else {
        fillstbl.emplace( orderAccount, [&]( auto& a ) {
          a.id = fillstbl.available_primary_key();
          a.hash = orderId;
          a.filled = order.amount.amount;
          a.expiration = signedTransaction.expiration.utc_seconds;
        });
      }
    }
};
