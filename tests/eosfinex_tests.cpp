#include <boost/test/unit_test.hpp>
#include <eosio/chain/wast_to_wasm.hpp>
#include <eosio/chain/authorization_manager.hpp>
#include <cstdlib>
#include <iostream>
#include <fc/log/logger.hpp>
#include <fc/io/raw.hpp>
#include <fc/crypto/sha256.hpp>
#include <fc/crypto/signature.hpp>
#include <eosio/chain/exceptions.hpp>
#include <eosio/chain/fixed_bytes.hpp>
#include <Runtime/Runtime.h>

#include "eosio.system_tester.hpp"

using namespace eosio_system;
using namespace eosio;
using namespace std;
using namespace fc::crypto;


const static account_name ME = account_name("eosfinex");
const static symbol core_symbol = symbol{CORE_SYM};
const static name system_account_name = eosio::chain::config::system_account_name;
struct currency_stats {
   asset    supply;
   asset    max_supply;
   name     issuer;
};
FC_REFLECT(currency_stats, (supply)(max_supply)(issuer));

struct account {
   asset    balance;
};
FC_REFLECT(account, (balance));

struct Order {
   uint32_t    seskey1;
   uint32_t    seskey2;
   uint64_t    nonce;
   asset       price;
   asset       amount;
   uint64_t    flags;

   static Order create(asset price, asset amount) {
      Order order;
      order.seskey1 = 0; // uint32_t
      order.seskey2 = 0; // uint32_t
      order.nonce   = 0; // uint64_t
      order.price   = price;
      order.amount  = amount;
      order.flags   = price.get_amount() == 0 ? 1 : 0; // uint64_t
      return order;
   }

   inline bool isBuy()              const noexcept { return amount.get_amount() > 0; }

   inline bool isMarketOrder()      const noexcept { return flags & 0b00000001; }
   inline bool isReleaseOnTrade()   const noexcept { return flags & 0b00000010; }
};
FC_REFLECT(Order, (seskey1)(seskey2)(nonce)(price)(amount)(flags));

struct Fill {
   uint64_t         id;
   checksum256_type hash;
   uint64_t         filled;
   uint32_t         expiration;
   uint64_t         reserved1;
};
FC_REFLECT(Fill, (id)(hash)(filled)(expiration)(reserved1));

struct assert_message_check {
   string _expected;
   assert_message_check(const string& expected) {
      _expected = expected;
   }

   bool operator()(const fc::exception& ex) {
      return eosio::testing::expect_assert_message(ex, _expected);
   }
};

static symbol_code EOS = symbol(0,"EOS").to_symbol_code();
static symbol_code USD = symbol(0,"USD").to_symbol_code();
static symbol_code EUR = symbol(0,"EUR").to_symbol_code();

struct eosfinex_tester : eosio_system_tester {
   
   abi_serializer eosfinex_abi;
   std::map< name, private_key> key_map;

   void add_key(name account, private_key pk) {
      key_map[account] = pk;
   }

   eosfinex_tester() {

      create_account_with_resources(ME, system_account_name, 5000000);
      set_authority( ME, N(active), {1, {{get_public_key(ME,"active"),1}}, {{{ME,N(eosio.code)},1}}} );

      // const auto& am = validating_node->get_authorization_manager();
      // const auto& p = am.get_permission({ME, N(active)});
      // auto s = fc::json::to_string(p, fc::time_point(abi_serializer_max_time));
      // BOOST_TEST_MESSAGE( "active perm: " << s );

      set_code(ME, contracts::eosfinex_wasm());
      set_abi(ME, contracts::eosfinex_abi().data());

      const auto& accnt = control->db().get<account_object,by_name>(ME);
      abi_def abi;
      BOOST_REQUIRE_EQUAL(abi_serializer::to_abi(accnt.abi, abi), true);
      eosfinex_abi.set_abi(abi, abi_serializer_max_time);
   }

   void create_token(const account_name& account, const asset& max_supply) {
      
      create_account_with_resources(account, system_account_name, 200e3);
      set_code( account, contracts::token_wasm());
      set_abi( account, contracts::token_abi().data() );

      create_currency( account, account, max_supply);
      issue(account, max_supply, account);
      
      BOOST_REQUIRE_EQUAL( max_supply, get_balance( account, account, max_supply.get_symbol() ) );
   }

   fc::variant get_token(const string& scode) {
      vector<char> data = get_row_by_account( ME, ME, N(listedtokens), account_name{symbol{0,scode.c_str()}.to_symbol_code()} );
      if(!data.size()) return fc::variant(nullptr);
      return eosfinex_abi.binary_to_variant( "listedtoken", data, abi_serializer_max_time );
   }

   fc::variant get_account(name accnt) {
      vector<char> data = get_row_by_account( ME, accnt, N(users), account_name{0} );
      if(!data.size()) return fc::variant(nullptr);
      return eosfinex_abi.binary_to_variant( "usr", data, abi_serializer_max_time );
   }

   fc::variant get_request(name accnt, const symbol_code& code) {
      vector<char> data = get_row_by_account( ME, accnt, N(requests), account_name{code.value} );
      if(!data.size()) return fc::variant(nullptr);
      return eosfinex_abi.binary_to_variant( "request", data, abi_serializer_max_time );
   }

   fc::variant get_internal_balance(name accnt, const symbol_code& code) {
      vector<char> data = get_row_by_account( ME, accnt, N(accounts), account_name{code.value} );
      if(!data.size()) return fc::variant(nullptr);
      return eosfinex_abi.binary_to_variant( "account", data, abi_serializer_max_time );
   }

   key256_t convert(const chain::checksum256_type& v) {
      // The input is in big endian, i.e. f58262c8005bb64b8f99ec6083faf050c502d099d9929ae37ffed2fe1bb954fb
      // fixed_bytes will convert the input to array of 2 uint128_t in little endian, i.e. 50f0fa8360ec998f4bb65b00c86282f5 fb54b91bfed2fe7fe39a92d999d002c5
      // which is the format used by secondary index
      uint8_t buffer[32];
      memcpy(buffer, v.data(), 32);
      fixed_bytes<32> fb(buffer); 
      return chain::key256_t(fb.get_array());
   };

   size_t get_total_fills() {
      auto& db = const_cast<chainbase::database&>(control->db());
      const auto* t_id = db.find<chain::table_id_object, chain::by_code_scope_table>( boost::make_tuple( ME, ME, N(fills) ) );
      if(t_id == nullptr || t_id->code != ME || t_id->scope != ME || t_id->table != N(fills)) return 0;

      //std::cout << "TOTAL: " << t_id->count << std::endl;
      const auto& idx = db.get_index<chain::key_value_index, chain::by_scope_primary>();
      size_t total=0;
      auto itr = idx.lower_bound( boost::make_tuple( t_id->id) );
      while(itr->t_id == t_id->id && itr != idx.end()) {
         // bytes data;
         // data.resize(itr->value.size());
         // memcpy(data.data(), itr->value.data(), itr->value.size());
         // std::cout << "TID: " << itr->t_id << std::endl
         //           << "PK:" << itr->primary_key << std::endl
         //           << "payer:" << itr->payer.to_string() << std::endl
         //           << "HEX:" << fc::to_hex(data.data(), data.size()) << std::endl;
         ++total;
         ++itr;
      }
      return total;
   }

   digest_type order_id(const signed_transaction& o) {
      return o.sig_digest(control->get_chain_id());
   }

   fc::variant get_fill_by_order(const signed_transaction& o) {
      auto hash = order_id(o);

      auto& db = const_cast<chainbase::database&>(control->db());
      const auto* t_id = db.find<chain::table_id_object, chain::by_code_scope_table>( boost::make_tuple( ME, ME, N(fills) ) );
      BOOST_REQUIRE(!(t_id == nullptr || t_id->code != ME || t_id->scope != ME || t_id->table != N(fills)));

      const auto& idx = db.get_index<chain::index256_index, chain::by_secondary>();

      auto seckey = convert(hash);
      auto itr = idx.lower_bound( boost::make_tuple( t_id->id, seckey) );
      
      BOOST_REQUIRE( itr != idx.end() && itr->t_id == t_id->id && seckey == itr->secondary_key );

      vector<char> data = get_row_by_account( ME, ME, N(fills), account_name{itr->primary_key} );
      if(!data.size()) return fc::variant(nullptr);
      return eosfinex_abi.binary_to_variant( "fill", data, abi_serializer_max_time );
   }

   template <typename Function>
   void raw_update(name code, name scope, name table, uint64_t id, Function&& f) {
      vector<char> data;
      auto& db = const_cast<chainbase::database&>(control->db());
      const auto* t_id = db.find<chain::table_id_object, chain::by_code_scope_table>( boost::make_tuple( code, scope, table ) );
      BOOST_REQUIRE(t_id != nullptr);

      const auto& idx = db.get_index<chain::key_value_index, chain::by_scope_primary>();
      auto itr = idx.lower_bound( boost::make_tuple( t_id->id, id ) );
      BOOST_REQUIRE( itr != idx.end() && itr->t_id == t_id->id && id == itr->primary_key );

      data.resize( itr->value.size() );
      memcpy( data.data(), itr->value.data(), data.size() );
      
      data = f(data);
      db.modify( *itr, [&]( auto& o ) {
         o.value.assign( data.data(), data.size() );
      });
   }

   int8_t hack_token_precision(name accnt, symbol_code code, uint8_t new_precision, const std::vector<name>& accnts) {
      
      int8_t old_precision;

      raw_update(accnt, name{code.value}, N(stat), code.value, [&](const auto& data) {
         auto cs = fc::raw::unpack<currency_stats>(data.data(), data.size());
         old_precision = cs.supply.get_symbol().decimals();

         auto new_symbol = symbol{new_precision, cs.supply.get_symbol().name().c_str()};

         cs.supply     = asset{cs.supply.get_amount(), new_symbol};
         cs.max_supply = asset{cs.max_supply.get_amount(), new_symbol};

         return fc::raw::pack(cs);
      });

      for(auto& a : accnts) {
         raw_update(accnt, a, N(accounts), code.value, [&](const auto& data) {
            auto ac = fc::raw::unpack<account>(data.data(), data.size());
            auto new_symbol = symbol{new_precision, ac.balance.get_symbol().name().c_str()};
            ac.balance = asset{ac.balance.get_amount(), new_symbol};
            return fc::raw::pack(ac);
         });
      }

      return old_precision;

   }

   std::string to_str(const fc::variant& o) {
      return fc::json::to_pretty_string(o, fc::time_point(fc::time_point::now()+abi_serializer_max_time) );
   }

   Order get_order(const signed_transaction& tx) {
      return fc::raw::unpack<Order>(tx.actions[0].data);
   }
   
   signed_transaction new_order(asset price, asset amount) {
      signed_transaction tx;
      tx.expiration             = time_point_sec(control->pending_block_time().sec_since_epoch()+600);
      tx.context_free_actions   = {};
      tx.transaction_extensions = {};
      tx.context_free_data      = {};

      auto order = Order::create(price, amount);
      tx.actions = {
         action {
            {
               permission_level{
                  name{0}, N(active)
               }
            }, 
            ME, N(place), 
            fc::raw::pack(order) //bytes((uint8_t*)&order, (uint8_t*)&order + sizeof(Order))
         }
      };
   
      return tx;
   }

   signed_transaction buy(asset amount) {
      return new_order(asset(0, amount.get_symbol()), amount);
   }

   signed_transaction sell(asset amount) {
      return new_order(asset(0, amount.get_symbol()), -amount);
   }

   signed_transaction buy(asset price, asset amount) {
      return new_order(price, amount);
   }

   signed_transaction sell(asset price, asset amount) {
      return new_order(price, -amount);
   }

   signed_transaction sign(signed_transaction tx, const private_key& key) {
      tx.signatures = { tx.sign(key, control->get_chain_id()) };
      return tx;
   }

   signed_transaction sign(signed_transaction tx, name account) {
      tx.signatures = { tx.sign(key_map[account], control->get_chain_id()) };
      return tx;
   }

   signed_transaction sign(signed_transaction tx) {
      tx.signatures = { tx.sign(key_map[tx.actions[0].authorization[0].actor], control->get_chain_id()) };
      return tx;
   }

   signed_transaction from(name account, signed_transaction tx) {
      tx.actions[0].authorization[0].actor = account;
      return tx;
   }

   signed_transaction nonce(uint64_t nonce, signed_transaction tx) {
      auto o = fc::raw::unpack<Order>(tx.actions[0].data);
      o.nonce = nonce;
      tx.actions[0].data = fc::raw::pack(o);
      return tx;
   }

   signed_transaction expiration(signed_transaction tx, time_point_sec exp) {
      tx.expiration = exp;
      return tx;
   }

   signed_transaction market_buy_as(name account, symbol pay_with, asset amount) {
      return sign(from(account, buy(asset(0, pay_with), amount)), key_map[account]);
   }

   signed_transaction buy_as(name account, asset price, asset amount, private_key pk=private_key()) {
      return sign(from(account, buy(price, amount)), pk == private_key() ? key_map[account] : pk);
   }

   signed_transaction buy_as(name account, asset price, asset amount, uint64_t n) {
      return sign(nonce(n, from(account, buy(price, amount))), key_map[account]);
   }

   signed_transaction market_sell_as(name account, symbol sell_for, asset amount) {
      return sign(from(account, sell(asset(0, sell_for), amount)), key_map[account]);
   }

   signed_transaction sell_as(name account, asset price, asset amount, private_key pk=private_key()) {
      return sign(from(account, sell(price, amount)), pk == private_key() ? key_map[account] : pk);
   }

   signed_transaction sell_as(name account, asset price, asset amount, uint64_t n) {
      return sign(nonce(n, from(account, sell(price, amount))), key_map[account]);
   }

   signed_transaction BAD_EXPIRATION(signed_transaction tx) {
      tx.expiration = fc::time_point_sec::min();
      return tx;
   }

   signed_transaction BAD_CONTEXT_FREE_ACTIONS(signed_transaction tx) {
      tx.context_free_actions = {action{}};
      return tx;
   }

   signed_transaction BAD_CONTEXT_FREE_DATA(signed_transaction tx) {
      tx.context_free_data = {{1,2,3}};
      return tx;
   }

   signed_transaction BAD_TRANSACTION_EXTENSIONS(signed_transaction tx) {
      tx.transaction_extensions = {{0,{1,2,3}}};
      return tx;
   }

   signed_transaction BAD_ACTION_COUNT(signed_transaction tx) {
      while(tx.actions.size() < 2)
         tx.actions.emplace_back(action{});
      return tx;
   }

   signed_transaction BAD_ACTION(signed_transaction tx) {
      tx.actions.clear();
      tx.actions.emplace_back(action{});
      return tx;
   }

   signed_transaction BAD_ACTION_ACCOUNT(signed_transaction tx) {
      if(tx.actions.size())
         tx.actions[0].account = N(bad.account);
      return tx;
   }
   
   signed_transaction BAD_ACTION_NAME(signed_transaction tx) {
      if(tx.actions.size())
         tx.actions[0].name = N(bad.name);
      return tx;
   }

   signed_transaction BAD_AUTHORIZATION_COUNT(signed_transaction tx) {
      if(tx.actions.size()){
         while(tx.actions[0].authorization.size() < 2)
            tx.actions[0].authorization.emplace_back(permission_level{});
      }
      return tx;
   }

   signed_transaction BAD_DATA_SIZE(signed_transaction tx) {
      if(tx.actions.size()){
         tx.actions[0].data.push_back(0);
      }
      return tx;
   }

   signed_transaction BAD_SIGNATURE_COUNT(signed_transaction tx) {
      while(tx.signatures.size() < 2)
         tx.signatures.emplace_back( signature_type() );
      return tx;
   }

   signed_transaction NEGATIVE_AMOUNT(signed_transaction tx) {
      auto o = fc::raw::unpack<Order>(tx.actions[0].data);
      o.amount = asset(-abs(o.amount.get_amount()) , o.amount.get_symbol());
      tx.actions[0].data = fc::raw::pack(o);
      return tx;
   }

   signed_transaction POSITIVE_AMOUNT(signed_transaction tx) {
      auto o = fc::raw::unpack<Order>(tx.actions[0].data);
      o.amount = asset(abs(o.amount.get_amount()) , o.amount.get_symbol());
      tx.actions[0].data = fc::raw::pack(o);
      return tx;
   }

   signed_transaction ZERO_AMOUNT(signed_transaction tx) {
      auto o = fc::raw::unpack<Order>(tx.actions[0].data);
      o.amount = asset(0, o.amount.get_symbol());
      tx.actions[0].data = fc::raw::pack(o);
      return tx;
   }

   action_result call( const name signer, const name cosigner, const action_name &name, const variant_object &data ) {

      string action_type_name = eosfinex_abi.get_action_type(name);

      vector<action> acts;
   
      // if( txpayer.to_uint64_t() ) {
      //    action act;
      //    act.authorization.push_back(permission_level{txpayer, N(active)});
      //    act.account       = ME;
      //    act.name          = N(nop);
      //    acts.emplace_back(std::move(act));
      // }
      
      action act;
      act.authorization.push_back(permission_level{signer, N(active)});
      act.account       = ME;
      act.name          = name;
      act.data          = eosfinex_abi.variant_to_binary( action_type_name, data, abi_serializer_max_time );

      if( cosigner.to_uint64_t() ) {
         act.authorization.push_back(permission_level{cosigner, N(active)});
      }

      acts.emplace_back(std::move(act));

      return my_push_action(std::move(acts));
   }

   static inline void print_debug(const action_trace& ar) {
      if (!ar.console.empty()) {
         cout << ": CONSOLE OUTPUT BEGIN =====================" << endl
            << ar.console << endl
            << ": CONSOLE OUTPUT END   =====================" << endl;
      }
   }

   transaction_trace_ptr last_tx_trace;
   action_result my_push_action(vector<action>&& acts) {
      signed_transaction trx;
      trx.actions = std::move(acts);

      set_transaction_headers(trx);
      for(const auto& act : trx.actions) {
         for(const auto& perm: act.authorization) {
            trx.sign(get_private_key(perm.actor, perm.permission.to_string()), control->get_chain_id());
         }
      }

      try {
         last_tx_trace = push_transaction(trx);
         if(true) {
            //print_debug(last_tx_trace->action_traces[0]);
         }
      } catch (const fc::exception& ex) {
         if(true) {
            // cout << "-----EXCEPTION------" << endl
            //      << "HEX: " << fc::json::to_string(trx.actions[0].data, fc::time_point(fc::time_point::now()+abi_serializer_max_time)) << endl
            //      << fc::json::to_string(ex, fc::time_point(fc::time_point::now()+abi_serializer_max_time)) << endl << endl;
         }
         edump((ex));
         edump((ex.to_detail_string()));
         return error(ex.top_message()); // top_message() is assumed by many tests; otherwise they fail
      }
      produce_block();
      BOOST_REQUIRE_EQUAL(true, chain_has_transaction(trx.id()));
      return success();
   }

   // - place action -

   action_result reguser( const name account, const public_key& pubkey, const uint32_t tos, name signer, name cosigner=ME ) {
      return call(signer, cosigner, N(reguser), mvo()
         ("account", account)
         ("pubkey",  pubkey)
         ("tos",     tos)
      );
   }

   action_result userkey( const name account, const public_key& pubkey, name signer, name cosigner=ME ) {
      return call(signer, cosigner, N(userkey), mvo()
         ("account", account)
         ("pubkey",  pubkey)
      );
   }

   action_result usertos( const name account, const uint32_t tos, name signer=name{0} ) {
      return call(signer == name{0} ? account : signer, name{0}, N(usertos), mvo()
         ("account", account)
         ("tos",  tos)
      );
   }

   action_result userstatus( const name account, const uint32_t status, name signer=ME ) {
      return call(signer, name{0}, N(userstatus), mvo()
         ("account", account)
         ("status",  status)
      );
   }

   action_result regtoken( const name account, const symbol_code token, int64_t minsize, name signer=ME ) {
      return call(signer, name{0}, N(regtoken), mvo()
         ("account", account)
         ("token",   token)
         ("minsize", minsize)
      );
   }

   // - validate action -

   action_result withdraw( const name account, const asset& quantity, name signer=name{0}) {
      return call(signer == name{0} ? account : signer, name{0}, N(withdraw), mvo()
         ("account",  account)
         ("quantity", quantity)
      );
   }

   action_result srvcwithdraw( const name account, const asset& quantity, name signer=ME ) {
      return call(signer, name{0}, N(srvcwithdraw), mvo()
         ("account",  account)
         ("quantity", quantity)
      );
   }

   action_result settle(  const uint64_t tradeId, const uint64_t buyOrderId, const uint64_t sellOrderId,
         const asset price, const asset amount, const int8_t buyFeeBps, const int8_t sellFeeBps,
         const signed_transaction& buyTransaction, const signed_transaction& sellTransaction, name signer=ME ) {

      return call(signer, name{0}, N(settle), mvo()
         ("tradeId", tradeId)
         ("buyOrderId", buyOrderId)
         ("sellOrderId", sellOrderId)
         ("price",  price)
         ("amount", amount)
         ("buyFeeBps",  buyFeeBps)
         ("sellFeeBps", sellFeeBps)
         ("buyTransation", buyTransaction)
         ("sellTransation", sellTransaction)
      );
   }

   action_result settle(const asset price, const asset amount, const int8_t buyFeeBps, const int8_t sellFeeBps,
               const signed_transaction& buyTransaction, const signed_transaction& sellTransaction ) {

      return settle(0, 0, 0, price, amount, buyFeeBps, sellFeeBps, buyTransaction, sellTransaction);
   }

   action_result settle(const asset price, const asset amount, const signed_transaction& buyTransaction,
                    const signed_transaction& sellTransaction ) {

      return settle(0, 0, 0, price, amount, 0, 0, buyTransaction, sellTransaction);
   }

   action_result settle(const signed_transaction& buyTransaction, const signed_transaction& sellTransaction ) {

      auto b = get_order(buyTransaction);
      auto s = get_order(sellTransaction);

      return settle(0, 0, 0, 
            b.price,
            std::min(b.amount, s.amount), 
            0, 0, buyTransaction, sellTransaction
      );
   }

   action_result prune( const uint32_t size, name signer=ME ) {
      return call(signer, name{0}, N(prune), mvo()
         ("size",  size)
      );
   }

   action_result cancel( const signed_transaction& order, name signer, name cosigner=ME ) {
      return call(signer, cosigner, N(cancel), mvo()
         ("signedTransaction", order)
      );
   }

   template< typename KeyType = fc::ecc::private_key_shim >
   auto generate_keypair() {
      auto pk = private_key_type::generate<KeyType>();
      return std::make_pair(pk, pk.get_public_key());
   }

   void setup_alice_bob(asset usd_token = asset::from_string("1000000.0000 USD"),
                        asset eos_token = asset::from_string("1000000.0000 EOS"),
                        asset to_alice  = asset::from_string("1000.0000 USD"),
                        asset to_bob    = asset::from_string("1000.0000 EOS"),
                        int64_t usd_minsize = 10000,
                        int64_t eos_minsize = 10000) {
      
      //create and register token USD
      create_token(N(usd), usd_token);
      BOOST_REQUIRE_EQUAL( regtoken(N(usd), usd_token.get_symbol().to_symbol_code(), usd_minsize),
                           success() );

      //create and register token USD
      create_token(N(eos), eos_token);
      BOOST_REQUIRE_EQUAL( regtoken(N(eos), eos_token.get_symbol().to_symbol_code(), eos_minsize),
                           success() );

      create_account_with_resources(N(alice), system_account_name);
      create_account_with_resources(N(bob), system_account_name);

      auto keys_a = generate_keypair();
      BOOST_REQUIRE_EQUAL( reguser(N(alice), keys_a.second, 1, N(alice), ME ), success() );
      add_key(N(alice), keys_a.first);

      auto keys_b = generate_keypair();
      BOOST_REQUIRE_EQUAL( reguser(N(bob), keys_b.second, 1, N(bob), ME ), success() );
      add_key(N(bob), keys_b.first);

      //issue USD to alice and deposit in to the exchange 
      transfer(N(usd), N(usd), N(alice), to_alice, N(usd));
      transfer(N(usd), N(alice), ME, to_alice, N(alice));

      //issue EOS to bob and deposit in to the exchange 
      transfer(N(eos), N(eos), N(bob), to_bob, N(eos));
      transfer(N(eos), N(bob), ME, to_bob, N(bob));
   }
};

BOOST_AUTO_TEST_SUITE(eosfinex_tests)

BOOST_FIXTURE_TEST_CASE( regtoken_test, eosfinex_tester ) try {
   
   create_account_with_resources(N(alice), system_account_name);
   
   //aaa account holds AAA token
   auto token = asset::from_string("1000000.0000 AAA");
   create_token(N(aaa), token);

   //bbb account has no code
   create_account_with_resources(N(bbb), system_account_name);

   BOOST_REQUIRE_EQUAL( regtoken(N(zzz), token.get_symbol().to_symbol_code(), -1, N(alice)),
                        error("missing authority of eosfinex") );

   BOOST_REQUIRE_EQUAL( regtoken(N(zzz), token.get_symbol().to_symbol_code(), -1),
                        wasm_assert_msg("Minsize must be >= 0") );

   BOOST_REQUIRE_EQUAL( regtoken(N(zzz), token.get_symbol().to_symbol_code(), 1000),
                        wasm_assert_msg("Issuer account does not exist") );

   BOOST_REQUIRE_EQUAL( regtoken(N(bbb), token.get_symbol().to_symbol_code(), 1000),
                        wasm_assert_msg("Issuer contract does not support that token") );

   BOOST_REQUIRE_EQUAL( regtoken(N(aaa), token.get_symbol().to_symbol_code(), 1000),
                        success() );
   
   REQUIRE_MATCHING_OBJECT( get_token("AAA"), mvo()
      ("token", "4,AAA")
      ("issuer", "aaa")
      ("minsize", "1000")
      ("reserved1", "0")
   );

   //Change minsize
   BOOST_REQUIRE_EQUAL( regtoken(N(aaa), token.get_symbol().to_symbol_code(), 500),
                        success() );

   REQUIRE_MATCHING_OBJECT( get_token("AAA"), mvo()
      ("token", "4,AAA")
      ("issuer", "aaa")
      ("minsize", "500")
      ("reserved1", "0")
   );

   //Error with an empty account
   BOOST_REQUIRE_EQUAL( regtoken(N(bbb), token.get_symbol().to_symbol_code(), 1000),
                        wasm_assert_msg("Issuer contract does not support that token") );

   //Error with different precision
   token = asset::from_string("1000000.000 AAA");
   create_token(N(ccc), token);
   BOOST_REQUIRE_EQUAL( regtoken(N(ccc), token.get_symbol().to_symbol_code(), 1000),
                        wasm_assert_msg("Precision mismatch") );
   
   //ddd account holds the new AAA token
   token = asset::from_string("1000000.0000 AAA");
   create_token(N(ddd), token);
   BOOST_REQUIRE_EQUAL( regtoken(N(ddd), token.get_symbol().to_symbol_code(), 300),
                        success() );

   REQUIRE_MATCHING_OBJECT( get_token("AAA"), mvo()
      ("token", "4,AAA")
      ("issuer", "ddd")
      ("minsize", "300")
      ("reserved1", "0")
   );

} FC_LOG_AND_RETHROW()

BOOST_FIXTURE_TEST_CASE( reguser_test, eosfinex_tester ) try {

   auto keys_a = generate_keypair();

   create_account_with_resources(N(alice), system_account_name);

   BOOST_REQUIRE_EQUAL( reguser(N(alice), keys_a.second, 1, N(alice1111111), ME),
                        error("missing authority of alice") );

   BOOST_REQUIRE_EQUAL( reguser(N(alice), keys_a.second, 1, N(alice), N(alice1111111)),
                        error("missing authority of eosfinex") );

   BOOST_REQUIRE_EQUAL( reguser(N(alice), keys_a.second, 1, N(alice), ME ),
                        success() );

   uint64_t v = (uint64_t(1) << 32 | uint64_t(1));
   REQUIRE_MATCHING_OBJECT( get_account(N(alice)), mvo()
      ("pubkey",    keys_a.second)
      ("status",    v)
      ("reserved1", "0")
   );

   keys_a = generate_keypair();
   BOOST_REQUIRE_EQUAL( reguser(N(alice), keys_a.second , 0, N(alice), ME),
                        wasm_assert_msg("User already registered") );

   create_account_with_resources(N(bob), system_account_name);

   BOOST_REQUIRE_EQUAL( reguser(N(bob), keys_a.second, 0, N(bob), ME ),
                        success() );

   v = (uint64_t(0) << 32 | uint64_t(1));
   REQUIRE_MATCHING_OBJECT( get_account(N(bob)), mvo()
      ("pubkey",    keys_a.second)
      ("status",    v)
      ("reserved1", "0")
   );

} FC_LOG_AND_RETHROW()

BOOST_FIXTURE_TEST_CASE( deposit_test, eosfinex_tester ) try {

   auto token_a = asset::from_string("1000000.0000 AAA");
   auto token_b = asset::from_string("1000000.0000 BBB");

   create_token(N(aaa), token_a );
   create_token(N(bbb), token_b );
   
   //Fake AAA token
   create_token(N(xxx), token_a );

   create_account_with_resources(N(alice), system_account_name);
   create_account_with_resources(N(bob), system_account_name);

   transfer(N(aaa), N(aaa), N(alice), asset::from_string("1000.0000 AAA"), N(aaa));
   transfer(N(xxx), N(xxx), N(alice), asset::from_string("1000.0000 AAA"), N(xxx));

   transfer(N(bbb), N(bbb), N(bob), asset::from_string("1000.0000 BBB"), N(bbb));

   //token not registered yet   
   BOOST_CHECK_EXCEPTION( transfer(N(aaa), N(alice), ME, asset::from_string("1000.0000 AAA"), N(alice)),
                        eosio_assert_message_exception, assert_message_check("Unknown token") );

   BOOST_REQUIRE_EQUAL( regtoken(N(aaa), token_a.get_symbol().to_symbol_code(), 1000),
                        success() );

   //same symbol different contract
   BOOST_CHECK_EXCEPTION( transfer(N(xxx), N(alice), ME, asset::from_string("10.0000 AAA"), N(alice)),
                        eosio_assert_message_exception, assert_message_check("Can only accept transfers of white listed tokens") );

   //same symbol / same contract (modified precision)
   auto oldp = hack_token_precision(N(aaa), symbol{0,"AAA"}.to_symbol_code(), 2, {N(alice)});
   
   BOOST_CHECK_EXCEPTION( transfer(N(aaa), N(alice), ME, asset::from_string("10.00 AAA"), N(alice)),
                        eosio_assert_message_exception, assert_message_check("Unsupported asset precision") );

   hack_token_precision(N(aaa), symbol{0,"AAA"}.to_symbol_code(), oldp, {N(alice)});

   //less than minimum
   BOOST_CHECK_EXCEPTION( transfer(N(aaa), N(alice), ME, asset::from_string("0.0999 AAA"), N(alice)),
                        eosio_assert_message_exception, assert_message_check("Transfer is less than the minimum required quantity") );

   //user not registered
   BOOST_CHECK_EXCEPTION( transfer(N(aaa), N(alice), ME, asset::from_string("0.1000 AAA"), N(alice)),
                        eosio_assert_message_exception, assert_message_check("Unknown user") );

   auto keys_a = generate_keypair();
   BOOST_REQUIRE_EQUAL( reguser(N(alice), keys_a.second, 1, N(alice), ME),
                        success() );

   //inactivate user
   BOOST_REQUIRE_EQUAL( userstatus(N(alice), 0, ME),
                        success() );
   
   BOOST_CHECK_EXCEPTION( transfer(N(aaa), N(alice), ME, asset::from_string("0.1000 AAA"), N(alice)),
                        eosio_assert_message_exception, assert_message_check("User status must be active in order to deposit funds") );

   BOOST_REQUIRE_EQUAL( userstatus(N(alice), 1, ME),
                        success() );

   //successful deposit of minimum amount
   transfer(N(aaa), N(alice), ME, asset::from_string("0.1000 AAA"), N(alice));

} FC_LOG_AND_RETHROW()

BOOST_FIXTURE_TEST_CASE( deposit_overflow_test, eosfinex_tester ) try {

   auto token_a = asset::from_string("461168601842.7387903 AAA");
   create_token(N(aaa), token_a );
   BOOST_REQUIRE_EQUAL( regtoken(N(aaa), token_a.get_symbol().to_symbol_code(), 1000),
                        success() );

   create_account_with_resources(N(alice), system_account_name);
   transfer(N(aaa), N(aaa), N(alice), asset::from_string("461168601842.7387903 AAA"), N(aaa));

   auto keys_a = generate_keypair();
   BOOST_REQUIRE_EQUAL( reguser(N(alice), keys_a.second, 1, N(alice), ME),
                        success() );

   //Overflow when normalizing to 8 decimals
   BOOST_CHECK_EXCEPTION( transfer(N(aaa), N(alice), ME, asset::from_string("461168601842.7387903 AAA"), N(alice)),
                        eosio_assert_message_exception, assert_message_check("Error normalizing value: overflow") );

} FC_LOG_AND_RETHROW()


BOOST_FIXTURE_TEST_CASE( withdraw_tests, eosfinex_tester ) try {

   auto token_a = asset::from_string("1000000.0000 AAA");
   auto token_b = asset::from_string("1000000.0000 BBB");

   create_token(N(aaa), token_a );
   create_token(N(bbb), token_b );
   
   create_account_with_resources(N(alice), system_account_name);
   create_account_with_resources(N(bob), system_account_name);

   transfer(N(aaa), N(aaa), N(alice), asset::from_string("1000.0000 AAA"), N(aaa));
   transfer(N(bbb), N(bbb), N(bob), asset::from_string("1000.0000 BBB"), N(bbb));

   auto keys_a = generate_keypair();
   BOOST_REQUIRE_EQUAL( reguser(N(alice), keys_a.second, true, N(alice), ME),
                        success() );

   BOOST_REQUIRE_EQUAL( regtoken(N(aaa), token_a.get_symbol().to_symbol_code(), 10000),
                        success() );

   //Alice deposit 100 AAA
   transfer(N(aaa), N(alice), ME, asset::from_string("100.0000 AAA"), N(alice));
   REQUIRE_MATCHING_OBJECT( get_internal_balance(N(alice), symbol{0,"AAA"}.to_symbol_code() ), mvo()
      ("balance", "100.00000000 AAA")
      ("reserved1", 0)
   );

   //Bob tries to withdraw 10 AAA from Alice
   BOOST_REQUIRE_EQUAL( withdraw(N(alice), asset::from_string("100.0000 AAA"), N(bob)),
                        wasm_assert_msg("Missing required authority") );

   //Alice tries to withdraw 100 BBB
   BOOST_REQUIRE_EQUAL( withdraw(N(alice), asset::from_string("100.000 BBB")),
                        wasm_assert_msg("Unknown token") );

   //Alice tries to withdraw 0 BBB
   BOOST_REQUIRE_EQUAL( withdraw(N(alice), asset::from_string("0.000 BBB")),
                        wasm_assert_msg("Unknown token") );

   //Alice tries to withdraw 101 AAA
   BOOST_REQUIRE_EQUAL( withdraw(N(alice), asset::from_string("101.0000 AAA")),
                        wasm_assert_msg("Insufficient balance for withdraw request") );

   //Alice tries to withdraw 50 AAA
   BOOST_REQUIRE_EQUAL( withdraw(N(alice), asset::from_string("50.0000 AAA")),
                        success() );

   REQUIRE_MATCHING_OBJECT( get_request(N(alice), symbol{0,"AAA"}.to_symbol_code() ), mvo()
      ("quantity", "50.0000 AAA")
      ("time", control->head_block_time().sec_since_epoch() )
      ("reserved1", 0)
   );

   //Alice tries to withdraw 20 AAA
   BOOST_REQUIRE_EQUAL( withdraw(N(alice), asset::from_string("20.0000 AAA")),
                        success() );

   REQUIRE_MATCHING_OBJECT( get_request(N(alice), symbol{0,"AAA"}.to_symbol_code() ), mvo()
      ("quantity", "70.0000 AAA")
      ("time", control->head_block_time().sec_since_epoch() )
      ("reserved1", 0)
   );

   //Alice tries to withdraw 0 AAA
   BOOST_REQUIRE_EQUAL( withdraw(N(alice), asset::from_string("0.0000 AAA")),
                        success() );

   BOOST_REQUIRE_EQUAL( get_request(N(alice), symbol{0,"AAA"}.to_symbol_code() ).is_null(),
                        fc::variant(nullptr).is_null());

   //Alice tries to withdraw 0 AAA (without having a pending withdraw)
   BOOST_REQUIRE_EQUAL( withdraw(N(alice), asset::from_string("0.0000 AAA")),
                        wasm_assert_msg("Must withdraw a positive amount") );

   //Alice tries to withdraw 10 AAA (wrong precision)
   BOOST_REQUIRE_EQUAL( withdraw(N(alice), asset::from_string("10.00000 AAA")),
                        wasm_assert_msg("Unsupported asset precision") );

} FC_LOG_AND_RETHROW()

BOOST_FIXTURE_TEST_CASE( srvcwithdraw_tests, eosfinex_tester ) try {

   auto token_a = asset::from_string("1000000.0000 AAA");
   create_token(N(aaa), token_a );
   create_account_with_resources(N(alice), system_account_name);
   transfer(N(aaa), N(aaa), N(alice), asset::from_string("1000.0000 AAA"), N(aaa));

   BOOST_REQUIRE_EQUAL( asset::from_string("1000.0000 AAA"),
                        get_balance( N(aaa), N(alice), token_a.get_symbol() ) );

   auto keys_a = generate_keypair();
   BOOST_REQUIRE_EQUAL( reguser(N(alice), keys_a.second, true, N(alice), ME),
                        success() );

   BOOST_REQUIRE_EQUAL( regtoken(N(aaa), token_a.get_symbol().to_symbol_code(), 10000),
                        success() );

   BOOST_REQUIRE_EQUAL( srvcwithdraw(N(alice), asset::from_string("30.0000 AAA")),
                        wasm_assert_msg("No pending withdraw request") );

   transfer(N(aaa), N(alice), ME, asset::from_string("100.0000 AAA"), N(alice));

   BOOST_REQUIRE_EQUAL( withdraw(N(alice), asset::from_string("70.0000 AAA")),
                        success() );

   REQUIRE_MATCHING_OBJECT( get_request(N(alice), symbol{0,"AAA"}.to_symbol_code() ), mvo()
      ("quantity", "70.0000 AAA")
      ("time", control->head_block_time().sec_since_epoch() )
      ("reserved1", 0)
   );

   REQUIRE_MATCHING_OBJECT( get_internal_balance(N(alice), symbol{0,"AAA"}.to_symbol_code() ), mvo()
      ("balance", "100.00000000 AAA")
      ("reserved1", 0)
   );

   //Call srvcwithdraw as alice (when elapsed time < EXCH_SERVICE_DELAY)
   BOOST_REQUIRE_EQUAL( srvcwithdraw(N(alice), asset::from_string("50.0000 AAA"), N(alice)),
                        error("missing authority of eosfinex") );

   //Call srvcwithdraw for 60 AAA (bad precision)
   BOOST_REQUIRE_EQUAL( srvcwithdraw(N(alice), asset::from_string("60.000 AAA")),
                        wasm_assert_msg("Incorrect quantity: Symbol must match request") );

   //Call srvcwithdraw for 70 AAA (bad precision)
   BOOST_REQUIRE_EQUAL( srvcwithdraw(N(alice), asset::from_string("70.000 AAA")),
                        wasm_assert_msg("Incorrect quantity: Symbol must match request") );

   //Call srvcwithdraw for 80 AAA (bad precision)
   BOOST_REQUIRE_EQUAL( srvcwithdraw(N(alice), asset::from_string("80.000 AAA")),
                        wasm_assert_msg("Incorrect quantity: Symbol must match request") );

   //Call srvcwithdraw for 140 AAA
   BOOST_REQUIRE_EQUAL( srvcwithdraw(N(alice), asset::from_string("140.0000 AAA")),
                        wasm_assert_msg("Incorrect quantity: Amount must be <= min of request and wallet balance") );

   //Call srvcwithdraw for 30 AAA
   BOOST_REQUIRE_EQUAL( srvcwithdraw(N(alice), asset::from_string("30.0000 AAA")),
                        success() );

   //Call srvcwithdraw for 40 AAA
   BOOST_REQUIRE_EQUAL( srvcwithdraw(N(alice), asset::from_string("40.0000 AAA")),
                        success() );
   
   REQUIRE_MATCHING_OBJECT( get_internal_balance(N(alice), symbol{0,"AAA"}.to_symbol_code() ), mvo()
      ("balance", "30.00000000 AAA")
      ("reserved1", 0)
   );

   BOOST_REQUIRE_EQUAL( asset::from_string("970.0000 AAA"),
                           get_balance( N(aaa), N(alice), token_a.get_symbol() ) );


} FC_LOG_AND_RETHROW()

#define A(X) eosio::chain::asset::from_string(X)

BOOST_FIXTURE_TEST_CASE( test_verify_transaction, eosfinex_tester ) try {

   create_account_with_resources(N(alice), system_account_name);
   create_account_with_resources(N(bob), system_account_name);
   create_account_with_resources(N(carol), system_account_name);

   auto keys_a = generate_keypair();
   BOOST_REQUIRE_EQUAL( reguser(N(alice), keys_a.second, 1, N(alice), ME ), success() );
   add_key(N(alice), keys_a.first);

   auto keys_b = generate_keypair();
   BOOST_REQUIRE_EQUAL( reguser(N(bob), keys_b.second, 1, N(bob), ME ), success() );
   add_key(N(bob), keys_b.first);

   auto keys_c = generate_keypair();
   //BOOST_REQUIRE_EQUAL( reguser(N(carol), keys_c.second, 1, N(carol), ME ), success() );
   add_key(N(carol), keys_c.first);

   //Order setup
   auto buy_order  = from( N(alice), buy(A("3.00000000 USD"),A("1.00000000 EOS")) );
   auto sell_order = from( N(bob), sell(A("3.00000000 USD"),A("1.00000000 EOS")) );

   //BAD_EXPIRATION
   BOOST_REQUIRE_EQUAL( settle(sign(BAD_EXPIRATION(buy_order)), sign(sell_order) ),
                        wasm_assert_msg("Signed buy transaction has expired") );
   BOOST_REQUIRE_EQUAL( settle(sign(buy_order), sign(BAD_EXPIRATION(sell_order))),
                        wasm_assert_msg("Signed sell transaction has expired") );

   //BAD_CONTEXT_FREE_ACTIONS
   BOOST_REQUIRE_EQUAL( settle(sign(BAD_CONTEXT_FREE_ACTIONS(buy_order)), sign(sell_order) ),
                        wasm_assert_msg("Singed buy transaction cannot have context free actions") );
   BOOST_REQUIRE_EQUAL( settle(sign(buy_order), sign(BAD_CONTEXT_FREE_ACTIONS(sell_order))),
                        wasm_assert_msg("Singed sell transaction cannot have context free actions") );

   //BAD_TRANSACTION_EXTENSIONS
   BOOST_REQUIRE_EQUAL( settle(sign(BAD_TRANSACTION_EXTENSIONS(buy_order)), sign(sell_order) ),
                        wasm_assert_msg("Signed buy transaction cannot have transaction extensions") );
   BOOST_REQUIRE_EQUAL( settle(sign(buy_order), sign(BAD_TRANSACTION_EXTENSIONS(sell_order))),
                        wasm_assert_msg("Signed sell transaction cannot have transaction extensions") );

   //BAD_SIGNATURE_COUNT
   BOOST_REQUIRE_EQUAL( settle(BAD_SIGNATURE_COUNT(sign(buy_order)), sign(sell_order) ),
                        wasm_assert_msg("Signed buy transaction can have only one sigature") );
   BOOST_REQUIRE_EQUAL( settle(sign(buy_order), BAD_SIGNATURE_COUNT(sign(sell_order))),
                        wasm_assert_msg("Signed sell transaction can have only one sigature") );

   //BAD_CONTEXT_FREE_DATA
   BOOST_REQUIRE_EQUAL( settle(BAD_CONTEXT_FREE_DATA(sign(buy_order)), sign(sell_order) ),
                        wasm_assert_msg("Signed buy transaction cannot have any context free data") );
   BOOST_REQUIRE_EQUAL( settle(sign(buy_order), BAD_CONTEXT_FREE_DATA(sign(sell_order))),
                        wasm_assert_msg("Signed sell transaction cannot have any context free data") );

   //BAD_ACTION_COUNT
   BOOST_REQUIRE_EQUAL( settle(sign(BAD_ACTION_COUNT(buy_order)), sign(sell_order) ),
                        wasm_assert_msg("Signed buy transaction can only have one action") );
   BOOST_REQUIRE_EQUAL( settle(sign(buy_order), sign(BAD_ACTION_COUNT(sell_order))),
                        wasm_assert_msg("Signed sell transaction can only have one action") );

   //BAD_ACTION_ACCOUNT
   BOOST_REQUIRE_EQUAL( settle(sign(BAD_ACTION_ACCOUNT(buy_order)), sign(sell_order) ),
                        wasm_assert_msg("Signed buy transaction's place action must reference this account") );
   BOOST_REQUIRE_EQUAL( settle(sign(buy_order), sign(BAD_ACTION_ACCOUNT(sell_order))),
                        wasm_assert_msg("Signed sell transaction's place action must reference this account") );

   //BAD_ACTION_NAME
   BOOST_REQUIRE_EQUAL( settle(sign(BAD_ACTION_NAME(buy_order)), sign(sell_order) ),
                        wasm_assert_msg("Signed buy transaction must contain the 'place' action") );
   BOOST_REQUIRE_EQUAL( settle(sign(buy_order), sign(BAD_ACTION_NAME(sell_order))),
                        wasm_assert_msg("Signed sell transaction must contain the 'place' action") );

   //BAD_AUTHORIZATION_COUNT
   BOOST_REQUIRE_EQUAL( settle(sign(BAD_AUTHORIZATION_COUNT(buy_order)), sign(sell_order) ),
                        wasm_assert_msg("Signed buy transaction's place action must have only one authorization") );
   BOOST_REQUIRE_EQUAL( settle(sign(buy_order), sign(BAD_AUTHORIZATION_COUNT(sell_order))),
                        wasm_assert_msg("Signed sell transaction's place action must have only one authorization") );

   //BAD_DATA_SIZE
   BOOST_REQUIRE_EQUAL( settle(sign(BAD_DATA_SIZE(buy_order)), sign(sell_order) ),
                        wasm_assert_msg("Incorrect size for signed buy transaction's place action") );
   BOOST_REQUIRE_EQUAL( settle(sign(buy_order), sign(BAD_DATA_SIZE(sell_order))),
                        wasm_assert_msg("Incorrect size for signed sell transaction's place action") );

   //USER NOT REGISTERED
   BOOST_REQUIRE_EQUAL( settle(sign(from(N(carol),buy_order), N(carol)), sign(sell_order)),
                        wasm_assert_msg("Unknown user") );
   BOOST_REQUIRE_EQUAL( settle(sign(buy_order), sign(from(N(carol),sell_order), N(carol))),
                        wasm_assert_msg("Unknown user") );

   //USER NOT ACTIVE
   BOOST_REQUIRE_EQUAL( userstatus(N(alice), 0, ME), success());
   BOOST_REQUIRE_EQUAL( settle(sign(buy_order), sign(sell_order)),
                        wasm_assert_msg("Signed buy transaction user status is not active") );
   BOOST_REQUIRE_EQUAL( userstatus(N(alice), 1, ME), success());

   BOOST_REQUIRE_EQUAL( userstatus(N(bob), 0, ME), success());
   BOOST_REQUIRE_EQUAL( settle(sign(buy_order), sign(sell_order)),
                        wasm_assert_msg("Signed sell transaction user status is not active") );
   BOOST_REQUIRE_EQUAL( userstatus(N(bob), 1, ME), success());

   //BAD SIGNATURE
   BOOST_REQUIRE_EQUAL( settle(sign(buy_order, N(bob)), sign(sell_order)),
                        wasm_assert_msg("Signed buy transaction signature is invalid for user's registered public key") );
   BOOST_REQUIRE_EQUAL( settle(sign(buy_order), sign(sell_order, N(alice))),
                        wasm_assert_msg("Signed sell transaction signature is invalid for user's registered public key") );

} FC_LOG_AND_RETHROW()

BOOST_FIXTURE_TEST_CASE( test_basic_order_checks, eosfinex_tester ) try {

   create_account_with_resources(N(alice), system_account_name);
   create_account_with_resources(N(bob), system_account_name);

   auto keys_a = generate_keypair();
   BOOST_REQUIRE_EQUAL( reguser(N(alice), keys_a.second, 1, N(alice), ME ), success() );
   add_key(N(alice), keys_a.first);

   auto keys_b = generate_keypair();
   BOOST_REQUIRE_EQUAL( reguser(N(bob), keys_b.second, 1, N(bob), ME ), success() );
   add_key(N(bob), keys_b.first);

   //Order setup
   auto buy_order  = buy_as(N(alice), A("3.00000000 USD"), A("1.00000000 EOS"));
   auto sell_order = sell_as(N(bob), A("3.00000000 USD"), A("1.00000000 EOS"));

   //check( price.amount > 0, "Settlement price must be positive" );
   BOOST_REQUIRE_EQUAL( settle( A("0.00 USD"), A("1.00 EOS"), buy_order, sell_order),
                        wasm_assert_msg("Settlement price must be positive") );
   BOOST_REQUIRE_EQUAL( settle( A("-1.00 USD"), A("1.00 EOS"), buy_order, sell_order),
                        wasm_assert_msg("Settlement price must be positive") );

   //check( amount.amount > 0, "Settlement amount must be positive" );
   BOOST_REQUIRE_EQUAL( settle( A("3.00 USD"), A("0.00 EOS"), buy_order, sell_order),
                        wasm_assert_msg("Settlement amount must be positive") );
   BOOST_REQUIRE_EQUAL( settle( A("3.00 USD"), A("-1.00 EOS"), buy_order, sell_order),
                        wasm_assert_msg("Settlement amount must be positive") );

   //check( price.symbol.precision() == EXCH_PRECISION, "Trade price must use exchange precision" );
   BOOST_REQUIRE_EQUAL( settle( A("3.00 USD"), A("1.00000000 EOS"), buy_order, sell_order),
                        wasm_assert_msg("Trade price must use exchange precision") );

   //check( amount.symbol.precision() == EXCH_PRECISION, "Trade amount must use exchange precision" );
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00 EOS"), buy_order, sell_order),
                        wasm_assert_msg("Trade amount must use exchange precision") );

   //check( buyFeeBps >= 0 && sellFeeBps >= 0, "Buy and sell fees must both be non-negative" );
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"), -1, -1, buy_order, sell_order),
                        wasm_assert_msg("Buy and sell fees must both be non-negative") );

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"),  0, -1, buy_order, sell_order),
                        wasm_assert_msg("Buy and sell fees must both be non-negative") );

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"),  -1, 0, buy_order, sell_order),
                        wasm_assert_msg("Buy and sell fees must both be non-negative") );

   //check( buyFeeBps <= 50 && sellFeeBps <= 50, "Buy and sell fees must both be less than 50 bps" );
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"), 51, 51, buy_order, sell_order),
                        wasm_assert_msg("Buy and sell fees must both be less than 50 bps") );

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"),  0, 51, buy_order, sell_order),
                        wasm_assert_msg("Buy and sell fees must both be less than 50 bps") );

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"),  51, 0, buy_order, sell_order),
                        wasm_assert_msg("Buy and sell fees must both be less than 50 bps") );
   
   //check( buyOrder.amount.amount  &&  buyOrder.isBuy(),  "Buy order must have positive amount" );
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"), 
                             sign(NEGATIVE_AMOUNT(buy_order)), sell_order),
                        wasm_assert_msg("Buy order must have positive amount") );
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"),
                             sign(ZERO_AMOUNT(buy_order)), sell_order),
                        wasm_assert_msg("Buy order must have positive amount") );

   //check( sellOrder.amount.amount && !sellOrder.isBuy(), "Sell order must have negative amount" );
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"),
                             buy_order, sign(POSITIVE_AMOUNT(sell_order))),
                        wasm_assert_msg("Sell order must have negative amount") );
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"),
                             buy_order, sign(ZERO_AMOUNT(sell_order))),
                        wasm_assert_msg("Sell order must have negative amount") );
   
   //check( amount.symbol == buyOrder.amount.symbol && price.symbol == buyOrder.price.symbol, "Buy order price/amount symbols must match trade price/amount symbols" );
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"),
                            buy_as(N(alice), A("3.00000000 USDT"), A("1.00000000 EOST")), sell_order),
                        wasm_assert_msg("Buy order price/amount symbols must match trade price/amount symbols") );

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"),
                            buy_as(N(alice), A("3.00000000 USD"), A("1.00000000 EOST")), sell_order),
                        wasm_assert_msg("Buy order price/amount symbols must match trade price/amount symbols") );

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"),
                            buy_as(N(alice), A("3.00000000 USDT"), A("1.00000000 EOS")), sell_order),
                        wasm_assert_msg("Buy order price/amount symbols must match trade price/amount symbols") );
   
   //check( amount.symbol == sellOrder.amount.symbol && price.symbol == sellOrder.price.symbol, "Sell order price/amount symbols must match trade price/amount symbols" );
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"),
                            buy_order, sell_as(N(alice), A("3.00000000 USDT"), A("1.00000000 EOST"))),
                        wasm_assert_msg("Sell order price/amount symbols must match trade price/amount symbols") );

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"),
                            buy_order, sell_as(N(alice), A("3.00000000 USD"), A("1.00000000 EOST"))),
                        wasm_assert_msg("Sell order price/amount symbols must match trade price/amount symbols") );

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"),
                            buy_order, sell_as(N(alice), A("3.00000000 USDT"), A("1.00000000 EOS"))),
                        wasm_assert_msg("Sell order price/amount symbols must match trade price/amount symbols") );
   
   //check( sellOrder.isMarketOrder() || sellOrder.price <= price, "Trade price would violate sell order price" );
   BOOST_REQUIRE_EQUAL( settle( A("2.99999999 USD"), A("1.00000000 EOS"), buy_order, sell_order),
                     wasm_assert_msg("Trade price would violate sell order price") );

   //check( buyOrder.isMarketOrder() ||  price <= buyOrder.price,  "Trade price would violate buy order price" );
   BOOST_REQUIRE_EQUAL( settle( A("3.00000001 USD"), A("1.00000000 EOS"), buy_order, sell_order),
                     wasm_assert_msg("Trade price would violate buy order price") );

   //New orders
   auto big_buy_order  = buy_as(N(alice), A("3.00000000 USD"), A("2.00000000 EOS"));
   
   //check( isValidQty( buyId,  amount.amount, buyOrder.amount.amount,  buyTransation.expiration ),  "Trade quantity would violate buy order quantity" );
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("2.00000001 EOS"), big_buy_order, sell_order),
                     wasm_assert_msg("Trade quantity would violate buy order quantity") );
   
   //check( isValidQty( sellId, amount.amount, sellOrder.amount.amount, sellTransation.expiration ), "Trade quantity would violate sell order quantity" );
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000001 EOS"), big_buy_order, sell_order),
                     wasm_assert_msg("Trade quantity would violate sell order quantity") );


} FC_LOG_AND_RETHROW()


BOOST_FIXTURE_TEST_CASE( trade_unregistered_tokens, eosfinex_tester ) try {
   create_account_with_resources(N(alice), system_account_name);
   create_account_with_resources(N(bob), system_account_name);

   auto keys_a = generate_keypair();
   BOOST_REQUIRE_EQUAL( reguser(N(alice), keys_a.second, 1, N(alice), ME ), success() );
   add_key(N(alice), keys_a.first);

   auto keys_b = generate_keypair();
   BOOST_REQUIRE_EQUAL( reguser(N(bob), keys_b.second, 1, N(bob), ME ), success() );
   add_key(N(bob), keys_b.first);

   //Order setup
   auto buy_order  = buy_as(N(alice), A("3.00000000 USD"), A("1.00000000 EOS"));
   auto sell_order = sell_as(N(bob), A("3.00000000 USD"), A("1.00000000 EOS"));

   //check( token != listedtokenstbl.end(), "Unknown token" );
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"), buy_order, sell_order),
                     wasm_assert_msg("Unknown token") );

   //create and register token USD
   auto usd_token = asset::from_string("1000000.0000 USD");
   create_token(N(usd), usd_token);
   BOOST_REQUIRE_EQUAL( regtoken(N(usd), usd_token.get_symbol().to_symbol_code(), 10000),
                        success() );

   //check( token != listedtokenstbl.end(), "Unknown token" );
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"), buy_order, sell_order),
                     wasm_assert_msg("Unknown token") );

   //create and register token USD
   create_token(N(eos), asset::from_string("1000000.0000 EOS"));
   auto eos_token = asset::from_string("1000000.0000 EOS");
   BOOST_REQUIRE_EQUAL( regtoken(N(eos), eos_token.get_symbol().to_symbol_code(), 10000),
                        success() );

   //alice has no USD to pay
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"), buy_order, sell_order),
                     wasm_assert_msg("Overdrawn balance for account alice 3.00000000 USD") );

   //issue USD to alice
   transfer(N(usd), N(usd), N(alice), asset::from_string("1000.0000 USD"), N(usd));
   
   //alice makes a deposit in to the exchange 
   transfer(N(usd), N(alice), ME, asset::from_string("10.0000 USD"), N(alice));

   //bob has no EOS to give
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"), buy_order, sell_order),
                     wasm_assert_msg("Overdrawn balance for account bob 1.00000000 EOS") );

   //issue EOS to bob
   transfer(N(eos), N(eos), N(bob), asset::from_string("1000.0000 EOS"), N(eos));
   
   //bob makes a deposit in to the exchange 
   transfer(N(eos), N(bob), ME, asset::from_string("1.0000 EOS"), N(bob));

   //successful trade
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"), buy_order, sell_order),
                     success() );

} FC_LOG_AND_RETHROW()


BOOST_FIXTURE_TEST_CASE( trade_same_order, eosfinex_tester ) try {

   setup_alice_bob();

   //Order setup
   auto buy_order   = buy_as(N(alice), A("3.00000000 USD"), A("10.00000000 EOS"));
   auto sell_order  = sell_as(N(bob),  A("3.00000000 USD"), A("5.00000000 EOS"));
   auto sell_order2 = sell_as(N(bob),  A("3.00000000 USD"), A("7.00000000 EOS"));

   //successful trade
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"), buy_order, sell_order),
                     success() );

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("3.00000000 EOS"), buy_order, sell_order),
                     success() );

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"), buy_order, sell_order),
                     success() );
   
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"), buy_order, sell_order),
                     wasm_assert_msg("Trade quantity would violate sell order quantity"));

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("5.00000000 EOS"), buy_order, sell_order2),
                     success());

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("2.00000000 EOS"), buy_order, sell_order2),
                     wasm_assert_msg("Trade quantity would violate buy order quantity"));

   REQUIRE_MATCHING_OBJECT( get_internal_balance(N(alice), symbol{0,"EOS"}.to_symbol_code() ), mvo()
      ("balance", "10.00000000 EOS")
      ("reserved1", 0)
   );

   REQUIRE_MATCHING_OBJECT( get_internal_balance(N(alice), symbol{0,"USD"}.to_symbol_code() ), mvo()
      ("balance", "970.00000000 USD")
      ("reserved1", 0)
   );

   REQUIRE_MATCHING_OBJECT( get_internal_balance(N(bob), symbol{0,"EOS"}.to_symbol_code() ), mvo()
      ("balance", "990.00000000 EOS")
      ("reserved1", 0)
   );

   REQUIRE_MATCHING_OBJECT( get_internal_balance(N(bob), symbol{0,"USD"}.to_symbol_code() ), mvo()
      ("balance", "30.00000000 USD")
      ("reserved1", 0)
   );

   BOOST_REQUIRE_EQUAL( get_fill_by_order(buy_order)["filled"].as_string(), "1000000000");
   BOOST_REQUIRE_EQUAL( get_fill_by_order(sell_order)["filled"].as_string(), "500000000");
   BOOST_REQUIRE_EQUAL( get_fill_by_order(sell_order2)["filled"].as_string(), "500000000");

} FC_LOG_AND_RETHROW()

BOOST_FIXTURE_TEST_CASE( order_expiration_test, eosfinex_tester ) try {

   setup_alice_bob();

   auto now = control->pending_block_time();

   //BOOST_TEST_MESSAGE( "t0: " << std::string(control->pending_block_time()) );

   auto buy_order   = sign(expiration(from(N(alice), buy(A("3.00000000 USD"), A("10.00000000 EOS"))), now+seconds(1)));
   auto sell_order  = sign(expiration(from(N(alice), sell(A("3.00000000 USD"), A("5.00000000 EOS"))), now+seconds(2)));

   //successful trade (+.5s)
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"), buy_order, sell_order),
                     success() );
   //BOOST_TEST_MESSAGE( "t1: " << std::string(control->pending_block_time()) );

   //successful trade (+.5s)
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"), buy_order, sell_order),
                     success() );
   BOOST_TEST_MESSAGE( "t2: " << std::string(control->pending_block_time()) );

   //Expired buy (+.5s)
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("1.00000000 EOS"), buy_order, sell_order),
                     wasm_assert_msg("Signed buy transaction has expired") );
   BOOST_TEST_MESSAGE( "t3: " << std::string(control->pending_block_time()) );

   //prune (+.5s)
   BOOST_REQUIRE_EQUAL( get_total_fills(), 2);
   BOOST_REQUIRE_EQUAL( prune(10), success() );

   //prune (+.5s) [sell expired]
   BOOST_REQUIRE_EQUAL( get_total_fills(), 1);
   produce_block();

   BOOST_REQUIRE_EQUAL( prune(10), success() );

   BOOST_REQUIRE_EQUAL( get_total_fills(), 0);

} FC_LOG_AND_RETHROW()

BOOST_FIXTURE_TEST_CASE( fee_test, eosfinex_tester ) try {

   setup_alice_bob();

   //Order setup
   auto buy_order   = buy_as(N(alice), A("3.00000000 USD"), A("20.00000000 EOS"));
   auto sell_order  = sell_as(N(bob),  A("3.00000000 USD"), A("20.00000000 EOS"));

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("10.00000000 EOS"), 
                                50, 0, buy_order, sell_order), success() );

   BOOST_REQUIRE_EQUAL( get_internal_balance( N(eosfinexfees), symbol{0,"EOS"}.to_symbol_code() )["balance"], 
        "0.05000000 EOS");

   BOOST_REQUIRE_EQUAL( get_internal_balance( N(eosfinexfees), symbol{0,"USD"}.to_symbol_code() ).is_null(),
        fc::variant(nullptr).is_null() );

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("10.00000000 EOS"), 
                                50, 50, buy_order, sell_order), success() );

   BOOST_REQUIRE_EQUAL( get_internal_balance( N(eosfinexfees), symbol{0,"EOS"}.to_symbol_code() )["balance"], 
        "0.10000000 EOS");

   BOOST_REQUIRE_EQUAL( get_internal_balance( N(eosfinexfees), symbol{0,"USD"}.to_symbol_code() )["balance"], 
        "0.15000000 USD");

} FC_LOG_AND_RETHROW()

BOOST_FIXTURE_TEST_CASE( small_amount_zero_fee, eosfinex_tester ) try {

   setup_alice_bob();

   //Order setup
   auto buy_order   = buy_as(N(alice), A("3.00000000 USD"), A("20.00000000 EOS"));
   auto sell_order  = sell_as(N(bob),  A("3.00000000 USD"), A("20.00000000 EOS"));

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("0.00000001 EOS"), 
                                50, 50, buy_order, sell_order), success() );

   BOOST_REQUIRE_EQUAL( get_internal_balance( N(eosfinexfees), symbol{0,"EOS"}.to_symbol_code() ).is_null(),
        fc::variant(nullptr).is_null() );

   BOOST_REQUIRE_EQUAL( get_internal_balance( N(eosfinexfees), symbol{0,"USD"}.to_symbol_code() ).is_null(),
        fc::variant(nullptr).is_null() );

} FC_LOG_AND_RETHROW()

BOOST_FIXTURE_TEST_CASE( normalized_asset_overflow_test, eosfinex_tester ) try {

   //8 (max) digits precision
   setup_alice_bob(
      asset::from_string("46116860184.27387903 USD"),
      asset::from_string("21000000.00000000 BTC"),
      asset::from_string("46116860184.27387903 USD"),
      asset::from_string("21000000.00000000 BTC"),
      1,
      1
   );

   //Overflow
   auto buy_order   = buy_as(N(alice), A("46116860184.27387903 USD"), A("10000.00000000 BTC"));
   auto sell_order  = sell_as(N(bob),  A("46116860184.27387903 USD"), A("10000.00000000 BTC"));
   BOOST_REQUIRE_EQUAL( settle( A("46116860184.27387903 USD"), A("10000.00000000 BTC"), 0, 0, buy_order, sell_order),
            wasm_assert_msg("Error normalizing value: overflow") );


} FC_LOG_AND_RETHROW()

BOOST_FIXTURE_TEST_CASE( trade_qty_buyfeebps_overflow_test, eosfinex_tester ) try {

   BOOST_REQUIRE_EQUAL( get_total_fills(), 0 );

   //8 (max) digits precision
   setup_alice_bob(
      asset::from_string("46116860184.27387903 USD"),
      asset::from_string("46116860184.27387903 EOS"),
      asset::from_string("46116860184.27387903 USD"),
      asset::from_string("46116860184.27387903 EOS"),
      1,
      1
   );

   BOOST_REQUIRE_EQUAL( get_total_fills(), 0 );

   //Overflow when buyFeeBps >= 2 (tradeQty * buyFeeBps / 10000)
   auto buy_order   = buy_as(N(alice), A("1.00000000 USD"), A("23058430092.13700000 EOS"));
   auto sell_order  = sell_as(N(bob),  A("1.00000000 USD"), A("23058430092.13700000 EOS"));
   BOOST_REQUIRE_EQUAL( settle( A("1.00000000 USD"), A("23058430092.13700000 EOS"), 2, 0, buy_order, sell_order),
            wasm_assert_msg("multiplication overflow") );

   BOOST_REQUIRE_EQUAL( get_total_fills(), 0 );

   //No Overflow when buyFeeBps <= 1 (tradeQty * buyFeeBps / 10000)
   buy_order   = buy_as(N(alice), A("1.00000000 USD"), A("46116860184.27387903 EOS"));
   sell_order  = sell_as(N(bob),  A("1.00000000 USD"), A("46116860184.27387903 EOS"));

   BOOST_REQUIRE_EQUAL( settle( A("1.00000000 USD"), A("46116860184.27387903 EOS"), 1, 0, buy_order, sell_order),
            success() );

   BOOST_REQUIRE_EQUAL( get_total_fills(), 2 );

} FC_LOG_AND_RETHROW()


BOOST_FIXTURE_TEST_CASE( trade_value_sellfeebps_overflow_test, eosfinex_tester ) try {

   BOOST_REQUIRE_EQUAL( get_total_fills(), 0 );

   //8 (max) digits precision
   setup_alice_bob(
      asset::from_string("46116860184.27387903 USD"),
      asset::from_string("46116860184.27387903 EOS"),
      asset::from_string("46116860184.27387903 USD"),
      asset::from_string("46116860184.27387903 EOS"),
      1,
      1
   );

   BOOST_REQUIRE_EQUAL( get_total_fills(), 0 );

   //Overflow when sellFeeBps >= 2 (sellFee = tradeValue * sellFeeBps / 10000)
   auto buy_order   = buy_as(N(alice), A("1.00000000 USD"), A("23058430092.13695000 EOS"));
   auto sell_order  = sell_as(N(bob),  A("1.00000000 USD"), A("23058430092.13695000 EOS"));
   BOOST_REQUIRE_EQUAL( settle( A("1.00000000 USD"), A("23058430092.13695000 EOS"), 0, 2, buy_order, sell_order),
            wasm_assert_msg("multiplication overflow") );

   BOOST_REQUIRE_EQUAL( get_total_fills(), 0 );

   //NO Overflow when sellFeeBps <= 1 (sellFee = tradeValue * sellFeeBps / 10000)
   buy_order   = buy_as(N(alice), A("1.00000000 USD"), A("46116860184.27387903 EOS"));
   sell_order  = sell_as(N(bob),  A("1.00000000 USD"), A("46116860184.27387903 EOS"));

   BOOST_REQUIRE_EQUAL( settle( A("1.00000000 USD"), A("46116860184.27387903 EOS"), 0, 1, buy_order, sell_order),
            success() );

   BOOST_REQUIRE_EQUAL( get_total_fills(), 2 );

} FC_LOG_AND_RETHROW()

BOOST_FIXTURE_TEST_CASE( small_resting_order_test, eosfinex_tester ) try {

   setup_alice_bob();

   auto buy_order   = buy_as(N(alice), A("3.00000000 USD"), A("0.99999999 EOS"));
   auto sell_order  = sell_as(N(bob),  A("3.00000000 USD"), A("1.00000000 EOS"));
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("0.99999999 EOS"), 0, 0, buy_order, sell_order),
            success() );

   BOOST_REQUIRE_EQUAL( get_total_fills(), 2 );

   auto same_balance = [&]() {
      REQUIRE_MATCHING_OBJECT( get_internal_balance( N(alice), symbol{4,"EOS"}.to_symbol_code() ), mvo()
         ("balance", "0.99999999 EOS")
         ("reserved1", 0)
      );
      REQUIRE_MATCHING_OBJECT( get_internal_balance( N(alice), symbol{4,"USD"}.to_symbol_code() ), mvo()
         ("balance", "997.00000003 USD")
         ("reserved1", 0)
      );

      REQUIRE_MATCHING_OBJECT( get_internal_balance( N(bob), symbol{4,"EOS"}.to_symbol_code() ), mvo()
         ("balance", "999.00000001 EOS")
         ("reserved1", 0)
      );
      REQUIRE_MATCHING_OBJECT( get_internal_balance( N(bob), symbol{4,"USD"}.to_symbol_code() ), mvo()
         ("balance", "2.99999997 USD")
         ("reserved1", 0)
      );
   };

   same_balance();
   BOOST_REQUIRE_EQUAL( get_fill_by_order(buy_order)["filled"].as_string(), "99999999");
   BOOST_REQUIRE_EQUAL( get_fill_by_order(sell_order)["filled"].as_string(), "99999999");

   // Now the contract will not throw "Error normalizing value: underflow"
   // Balances of involved actions wont change, but the order is consumed
   buy_order   = buy_as(N(alice), A("3.00000000 USD"), A("0.00000001 EOS"));
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("0.00000001 EOS"), 0, 0, buy_order, sell_order),
            success() );


   //TODO: check new balance here
   //same_balance();

   //TODO: why?
   // BOOST_REQUIRE_EQUAL( get_fill_by_order(buy_order)["filled"].as_string(), "10000000000");
   // BOOST_REQUIRE_EQUAL( get_fill_by_order(sell_order)["filled"].as_string(),"10000000000");

   //Check the order is fully filled
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("0.00000001 EOS"), 0, 0, buy_order, sell_order),
            wasm_assert_msg("Trade quantity would violate buy order quantity") );


} FC_LOG_AND_RETHROW()


BOOST_FIXTURE_TEST_CASE( market_order_test, eosfinex_tester ) try {

   setup_alice_bob();

   auto buy_order   = market_buy_as(N(alice), symbol(SY(8,USD)), A("10.00000000 EOS"));
   auto sell_order  = sell_as(N(bob), A("3.00000000 USD"), A("10.00000000 EOS"));
   
   BOOST_REQUIRE_EQUAL( settle( A("3.10000000 USD"), A("5.00000000 EOS"), 50, 50, buy_order, sell_order),
            success() );
   
   sell_order  = market_sell_as(N(bob), symbol(SY(8,USD)), A("1.00000000 EOS"));
   
   BOOST_REQUIRE_EQUAL( settle( A("2.70000000 USD"), A("1.00000000 EOS"), 50, 50, buy_order, sell_order),
            success() );

   sell_order  = market_sell_as(N(bob), symbol(SY(8,USD)), A("4.00000000 EOS"));
   
   BOOST_REQUIRE_EQUAL( settle( A("6.70000000 USD"), A("3.99999999 EOS"), 50, 50, buy_order, sell_order),
            success() );

   auto USD = symbol{8,"USD"};
   asset total_usd(0, USD);
   total_usd += get_internal_balance( N(alice), USD.to_symbol_code() )["balance"].as<asset>();
   total_usd += get_internal_balance( N(bob), USD.to_symbol_code() )["balance"].as<asset>();
   total_usd += get_internal_balance( N(eosfinexfees), USD.to_symbol_code() )["balance"].as<asset>();

   auto EOS = symbol{8,"EOS"};
   asset total_eos(0, EOS);
   total_eos += get_internal_balance( N(alice), EOS.to_symbol_code() )["balance"].as<asset>();
   total_eos += get_internal_balance( N(bob), EOS.to_symbol_code() )["balance"].as<asset>();
   total_eos += get_internal_balance( N(eosfinexfees), EOS.to_symbol_code() )["balance"].as<asset>();
   
   BOOST_REQUIRE_EQUAL( total_usd.to_string(), "1000.00000000 USD" );
   BOOST_REQUIRE_EQUAL( total_eos.to_string(), "1000.00000000 EOS" ); 


} FC_LOG_AND_RETHROW()


BOOST_FIXTURE_TEST_CASE( cancel_order_test, eosfinex_tester ) try {

   setup_alice_bob();

   auto buy_order  = buy_as(N(alice), A("3.00000000 USD"), A("10.00000000 EOS"));
   auto sell_order = sell_as(N(bob), A("3.00000000 USD"), A("10.00000000 EOS"));

   BOOST_REQUIRE_EQUAL( get_total_fills(), 0 );

   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("5.00000000 EOS"), 50, 50, buy_order, sell_order),
            success() );

   BOOST_REQUIRE_EQUAL( get_total_fills(), 2 );

   //Bob tries to cancel Alice order
   BOOST_REQUIRE_EQUAL( cancel(buy_order, N(bob)), error("missing authority of alice") );

   //Alice tries to cancel without eosfinex
   BOOST_REQUIRE_EQUAL( cancel(buy_order, N(alice), N(bob)), error("missing authority of eosfinex") );

   //Ok
   BOOST_REQUIRE_EQUAL( cancel(buy_order, N(alice)), success() );

   //Error trying to cancel an already canceled order
   BOOST_REQUIRE_EQUAL( cancel(buy_order, N(alice)), 
         wasm_assert_msg("Order is already marked as fully filled"));

   auto never_submited  = buy_as(N(bob), A("6.00000000 USD"), A("10.00000000 EOS"));

   //Ok
   BOOST_REQUIRE_EQUAL( cancel(never_submited, N(bob)), success() );

   //Error trying to cancel an already canceled order
   BOOST_REQUIRE_EQUAL( cancel(never_submited, N(bob)), 
         wasm_assert_msg("Order is already marked as fully filled"));

   //Error trying to settle a cancelled order
   BOOST_REQUIRE_EQUAL( settle( A("3.00000000 USD"), A("5.00000000 EOS"), 50, 50, buy_order, sell_order),
            wasm_assert_msg("Trade quantity would violate buy order quantity") );

   BOOST_REQUIRE_EQUAL( get_total_fills(), 3 );

} FC_LOG_AND_RETHROW()

BOOST_AUTO_TEST_SUITE_END()
