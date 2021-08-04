use super::*;
use frame_election_provider_support::VoteWeight;
use frame_support::parameter_types;
use std::cell::RefCell;

type AccountId = u32;
type Balance = u32;

thread_local! {
	static VOTE_WEIGHT: RefCell<VoteWeight> = RefCell::new(Default::default())
}

/// Set a mock return value for `StakingVoteWeight::staking_vote_weight`.
pub(crate) fn set_staking_vote_weight(weight: VoteWeight) {
	VOTE_WEIGHT.with(|w| *w.borrow_mut() = weight);
}

pub struct StakingMock;
impl frame_election_provider_support::StakingVoteWeight<AccountId> for StakingMock {
	fn staking_vote_weight(_who: &AccountId) -> VoteWeight {
		VOTE_WEIGHT.with(|h| h.borrow().clone())
	}
}

impl frame_system::Config for Runtime {
	type SS58Prefix = ();
	type BaseCallFilter = frame_support::traits::AllowAll;
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = sp_core::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = AccountId;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Header = sp_runtime::testing::Header;
	type Event = Event;
	type BlockHashCount = ();
	type DbWeight = ();
	type BlockLength = ();
	type BlockWeights = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<Balance>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type OnSetCode = ();
}

/// Thresholds used for bags.
const THRESHOLDS: [VoteWeight; 9] = [10, 20, 30, 40, 50, 60, 1_000, 2_000, 10_000];

parameter_types! {
	pub const BagThresholds: &'static [VoteWeight] = &THRESHOLDS;
}

impl crate::Config for Runtime {
	type Event = Event;
	type BagThresholds = BagThresholds;
	type StakingVoteWeight = StakingMock;
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Runtime>;
type Block = frame_system::mocking::MockBlock<Runtime>;
frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Storage, Event<T>, Config},
		PalletBagsList: crate::{Pallet, Call, Storage, Event<T>},
	}
);

pub(crate) mod ext_builder {
	use super::*;

	/// Default AccountIds and their weights.
	const GENESIS_IDS: [(AccountId, VoteWeight); 4] =
		[(31, 10), (11, 1_000), (21, 1_000), (101, 1_000)];
	#[derive(Default)]
	pub(crate) struct ExtBuilder {
		ids: Vec<(AccountId, VoteWeight)>,
	}

	impl ExtBuilder {
		/// Add some AccountIds to insert into `List`.
		pub(crate) fn add_ids(mut self, ids: Vec<(AccountId, VoteWeight)>) -> Self {
			self.ids = ids;
			self
		}

		pub(crate) fn build(self) -> sp_io::TestExternalities {
			sp_tracing::try_init_simple();
			let storage =
				frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();

			let mut ext = sp_io::TestExternalities::from(storage);
			ext.execute_with(|| {
				for (id, weight) in GENESIS_IDS.iter().chain(self.ids.iter()) {
					List::<Runtime>::insert(*id, *weight);
				}
			});

			ext
		}

		pub(crate) fn build_and_execute(self, test: impl FnOnce() -> ()) {
			self.build().execute_with(test);
		}
	}
}

pub(crate) mod test_utils {
	use super::*;
	use list::Bag;

	/// Returns the nodes of all non-empty bags.
	pub(crate) fn get_bags() -> Vec<(VoteWeight, Vec<AccountId>)> {
		BagThresholds::get()
			.into_iter()
			.filter_map(|t| {
				Bag::<Runtime>::get(*t)
					.map(|bag| (*t, bag.iter().map(|n| n.id().clone()).collect::<Vec<_>>()))
			})
			.collect::<Vec<_>>()
	}

	pub(crate) fn bag_as_ids(bag: &Bag<Runtime>) -> Vec<AccountId> {
		bag.iter().map(|n| *n.id()).collect::<Vec<_>>()
	}

	pub(crate) fn get_voter_list_as_ids() -> Vec<AccountId> {
		List::<Runtime>::iter().map(|n| *n.id()).collect::<Vec<_>>()
	}
}
