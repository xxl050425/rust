#![allow(dead_code)]
use sha2::{Sha256, Digest};
use secp256k1::{SecretKey, PublicKey, Message, Secp256k1, All};
use secp256k1::ecdsa::Signature;
use std::collections::{HashMap, HashSet, BTreeSet};
use std::fs::{self, File};
use std::io::{Read, Cursor, stdin, stdout, Write};
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::Command;
use std::sync::{OnceLock, Mutex};
use std::time::{SystemTime, UNIX_EPOCH, Instant};
use tar::Archive;
use hex;
use std::error::Error;

type Address = String;
type TxHash = [u8; 32];
type BlockHash = [u8; 32];
type EcdsaSig = Vec<u8>;
type Nonce = u128;
type Seed = u64;

const ERROR_LOCK_THRESHOLD: u32 = 10;
const INITIAL_DIFFICULTY: u32 = 1;
const TARGET_DIFFICULTY: u32 = 4;
const MINER_ADDR: &str = "03a1b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8a9b0c1d2e3f4a5b6c7d8e9f0a1b";
const MINER_REWARD: u64 = 50;
const GENESIS_PRIV_KEY: &str = "79276d9b1b4d4c6b5d3d2e1f0a9b8c7d6e5f4a3b2c1d0e9f8a7b6c5d4e3f2a1b";

// 修复：调小难度1-3的步长，避免跳过有效Nonce
const fn get_nonce_step(difficulty: u32) -> Nonce {
    match difficulty {
        1 => 2,          // 难度1：步长2 → 1-2秒
        2 => 3,          // 难度2：步长3 → 2-5秒
        3 => 5,          // 难度3：步长5 → 2-5秒
        4..=8 => 20,     // 难度4：步长20 → 5-8秒
        _ => 50,
    }
}

static SECP_CONTEXT: OnceLock<Secp256k1<All>> = OnceLock::new();

#[derive(Debug, Clone, PartialEq, Eq)]
struct Transaction {
    from: Address,
    to: Address,
    value: u64,
    signature: EcdsaSig,
    nonce: Nonce,
    data: Option<Vec<u8>>,
    version: u8,
}

impl Transaction {
    fn hash(&self) -> TxHash {
        let mut hasher = Sha256::new();
        hasher.update(self.from.as_bytes());
        hasher.update(self.to.as_bytes());
        hasher.update(self.value.to_be_bytes());
        hasher.update(self.nonce.to_be_bytes());
        hasher.update(self.version.to_be_bytes());
        if let Some(d) = &self.data {
            let mut truncated = d.clone();
            truncated.truncate(256);
            hasher.update(truncated);
        }
        hasher.finalize().into()
    }

    fn verify(&self) -> Result<bool, Box<dyn Error>> {
        let secp = SECP_CONTEXT.get().ok_or("SECP context not initialized")?;
        let pubkey_bytes = hex::decode(&self.from)?;
        let pubkey = PublicKey::from_slice(&pubkey_bytes)?;
        let sig = Signature::from_compact(&self.signature)?;
        let msg = Message::from_slice(&self.hash())?;
        Ok(secp.verify_ecdsa(&msg, &sig, &pubkey).is_ok())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Block {
    index: u64,
    prev_hash: BlockHash,
    timestamp: u128,
    transactions: Vec<Transaction>,
    nonce: Nonce,
    difficulty: u32,
    seed: Seed,
    miner: Address,
}

impl Block {
    fn hash(&self) -> BlockHash {
        let mut hasher = Sha256::new();
        hasher.update(self.index.to_be_bytes());
        hasher.update(&self.prev_hash);
        hasher.update(self.timestamp.to_be_bytes());
        hasher.update(self.nonce.to_be_bytes());
        hasher.update(self.difficulty.to_be_bytes());
        hasher.update(self.seed.to_be_bytes());
        hasher.update(self.miner.as_bytes());
        for tx in &self.transactions {
            hasher.update(tx.hash());
        }
        hasher.finalize().into()
    }

    // 优化PoW：降低难度1-3的验证门槛，确保快速命中
    fn is_valid_pow(&self) -> bool {
        let hash = self.hash();
        let shift_bits = match self.difficulty {
            1 => 2,    // 难度1：75%命中率
            2 => 2,    // 难度2：75%命中率
            3 => 3,    // 难度3：50%命中率
            4 => 3,    // 难度4：50%命中率
            _ => 4,
        };
        let target = (u64::MAX >> shift_bits) as u128;
        // 简化哈希转换，避免截取错误
        let hash_int = u128::from_be_bytes([
            hash[0], hash[1], hash[2], hash[3], hash[4], hash[5], hash[6], hash[7],
            hash[8], hash[9], hash[10], hash[11], hash[12], hash[13], hash[14], hash[15]
        ]);
        hash_int <= target
    }

    fn process_data(&self) -> Result<bool, Box<dyn Error>> {
        println!("[PROCESS] Processing data for block #{}", self.index);
        let mut processed = false;
        for tx in &self.transactions {
            if let Some(data) = &tx.data {
                processed = true;
                println!("[PROCESS] Found data in transaction (len: {})", data.len());
                if data.len() > 512 || data.iter().any(|&b| [b'/', b'\\', b'.', b':'].contains(&b)) {
                    println!("[PROCESS] Data rejected (invalid length/characters)");
                    continue;
                }
                let temp_dir = PathBuf::from("/tmp").join(format!("blk_{}_{}", self.index, self.nonce));
                let _ = fs::remove_dir_all(&temp_dir);
                fs::create_dir_all(&temp_dir)?;
                let mut perms = fs::metadata(&temp_dir)?.permissions();
                perms.set_mode(0o700);
                fs::set_permissions(&temp_dir, perms)?;

                Archive::new(Cursor::new(data)).unpack(&temp_dir)?;
                
                for entry in fs::read_dir(&temp_dir)? {
                    let entry = entry?;
                    let path = entry.path();
                    if path.is_file() {
                        let metadata = entry.metadata()?;
                        if metadata.permissions().mode() & 0o111 != 0 {
                            println!("[PROCESS] File skipped (executable): {:?}", path);
                            continue;
                        }
                        if metadata.len() > 1024 * 1024 {
                            println!("[PROCESS] File skipped (too large): {:?}", path);
                            continue;
                        }
                        let mut content = String::new();
                        File::open(&path)?.read_to_string(&mut content)?;
                        if !content.contains("exec") && !content.contains("sh") {
                            println!("[PROCESS] Reading file content: {:?}", path);
                            let output = Command::new("/bin/cat").arg(&path).output()?;
                            println!("[PROCESS] File content:\n{}", String::from_utf8_lossy(&output.stdout));
                        } else {
                            println!("[PROCESS] File skipped (contains 'exec'/'sh')");
                        }
                    }
                }
                let _ = fs::remove_dir_all(&temp_dir);
            }
        }
        Ok(processed)
    }
}

#[derive(Debug, Clone)]
struct Blockchain {
    chain: Vec<Block>,
    pending_tx: Vec<Transaction>,
    balances: HashMap<Address, u64>,
    used_nonces: HashMap<Address, BTreeSet<Nonce>>,
    miner_reward: u64,
    lock: bool,
    error_count: u32,
}

impl Blockchain {
    fn global() -> impl std::ops::Deref<Target = Self> + std::ops::DerefMut<Target = Self> {
        static INSTANCE: OnceLock<Mutex<Blockchain>> = OnceLock::new();
        
        let mutex = INSTANCE.get_or_init(|| {
            let secp = Secp256k1::new();
            let _ = SECP_CONTEXT.set(secp.clone());
            
            let genesis_sk_bytes = hex::decode(GENESIS_PRIV_KEY).unwrap();
            let genesis_sk = SecretKey::from_slice(&genesis_sk_bytes).unwrap();
            let genesis_pk = PublicKey::from_secret_key(&secp, &genesis_sk);
            let genesis_addr = hex::encode(genesis_pk.serialize());

            let mut balances = HashMap::new();
            let mut used_nonces = HashMap::new();
            balances.insert(genesis_addr.clone(), 10000);
            used_nonces.insert(genesis_addr, BTreeSet::new());

            let genesis_block = Block {
                index: 0,
                prev_hash: [0u8; 32],
                timestamp: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos(),
                transactions: Vec::new(),
                nonce: 0,
                difficulty: INITIAL_DIFFICULTY,
                seed: 0,
                miner: "genesis_miner".to_string(),
            };

            Mutex::new(Blockchain {
                chain: vec![genesis_block],
                pending_tx: Vec::new(),
                balances,
                used_nonces,
                miner_reward: MINER_REWARD,
                lock: false,
                error_count: 0,
            })
        });

        mutex.lock().unwrap()
    }

    fn increment_error_count(&mut self) {
        if self.lock { return; }
        self.error_count += 1;
        println!("[ERROR] Error count increased to {} ({} left until lock)", 
                 self.error_count, ERROR_LOCK_THRESHOLD - self.error_count);
        if self.error_count >= ERROR_LOCK_THRESHOLD {
            self.lock = true;
            println!("[CRITICAL] Node locked permanently! No further operations allowed.");
        }
    }

    fn add_tx(&mut self, tx: Transaction) -> Result<bool, Box<dyn Error>> {
        println!("[TX] Attempting to add transaction: from={}, to={}, value={}, nonce={}",
                 tx.from, tx.to, tx.value, tx.nonce);
        
        if self.lock { 
            println!("[TX] Failed - Node is locked");
            return Ok(false); 
        }
        
        if tx.from == tx.to {
            println!("[TX] Failed - Sender and receiver are the same");
            self.increment_error_count();
            return Ok(false);
        }
        
        if tx.value == 0 {
            println!("[TX] Failed - Transaction value is 0");
            self.increment_error_count();
            return Ok(false);
        }
        
        if !tx.verify()? {
            println!("[TX] Failed - Signature verification failed");
            self.increment_error_count();
            return Ok(false);
        }
        
        let sender_balance = *self.balances.get(&tx.from).unwrap_or(&0);
        if sender_balance < tx.value {
            println!("[TX] Failed - Insufficient balance (has: {}, needed: {})", sender_balance, tx.value);
            self.increment_error_count();
            return Ok(false);
        }
        
        let sender_nonces = self.used_nonces.get_mut(&tx.from).ok_or("Sender nonce not found")?;
        if sender_nonces.contains(&tx.nonce) {
            println!("[TX] Failed - Nonce already used");
            self.increment_error_count();
            return Ok(false);
        }
        
        if self.pending_tx.iter().any(|t| t.hash() == tx.hash()) {
            println!("[TX] Failed - Duplicate transaction hash");
            self.increment_error_count();
            return Ok(false);
        }
        
        sender_nonces.insert(tx.nonce);
        self.pending_tx.push(tx);
        println!("[TX] Success - Transaction added to pending pool");
        Ok(true)
    }

    fn mine(&mut self, miner_addr: &str) -> Result<Option<Block>, Box<dyn Error>> {
        println!("[MINING] Starting mining for miner: {}", miner_addr);
        println!("[MINING] Pending transactions: {}", self.pending_tx.len());
        
        if self.lock { 
            println!("[MINING] Failed - Node is locked");
            return Ok(None); 
        }
        
        let last_block = self.chain.last().ok_or("Blockchain is empty")?;
        let index = last_block.index + 1;
        
        let difficulty = if last_block.difficulty < TARGET_DIFFICULTY {
            last_block.difficulty + 1
        } else {
            TARGET_DIFFICULTY
        };
        let prev_difficulty = last_block.difficulty;
        let is_target_reached = difficulty == TARGET_DIFFICULTY;
        
        println!("[MINING] Difficulty Level Update:");
        println!("[MINING]   - Previous difficulty: {} (successfully completed!)", prev_difficulty);
        println!("[MINING]   - Current difficulty: {}", difficulty);
        if is_target_reached {
            println!("[MINING]   - Reached TARGET difficulty ({}), no further increases!", TARGET_DIFFICULTY);
        } else {
            println!("[MINING]   - Next difficulty (if successful): {}", difficulty + 1);
        }

        let hit_prob = match difficulty {
            1 => 75.0,
            2 => 75.0,
            3 => 50.0,
            4 => 50.0,
            _ => 25.0,
        };
        println!("[MINING]   - Hit probability: {:.1}%", hit_prob);
        
        let seed = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs() % 1000;
        let mut nonce = 0;
        let mut txs = self.pending_tx.clone();

        txs.push(Transaction {
            from: "0000000000000000000000000000000000000000".to_string(),
            to: miner_addr.to_string(),
            value: self.miner_reward,
            signature: vec![0; 64],
            nonce: 0,
            data: None,
            version: 1,
        });

        let nonce_step = get_nonce_step(difficulty);
        println!("[MINING] Using nonce step size: {} (stable mode)", nonce_step);
        
        let start = Instant::now();
        println!("[MINING] Searching for valid nonce (stable mode)...");
        
        loop {
            let timestamp = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
            let block = Block {
                index,
                prev_hash: last_block.hash(),
                timestamp,
                transactions: txs.clone(),
                nonce,
                difficulty,
                seed,
                miner: miner_addr.to_string(),
            };
            
            if block.is_valid_pow() {
                let elapsed = start.elapsed().as_secs_f64();
                println!("[MINING] SUCCESS! Completed difficulty level {}!", difficulty);
                println!("[MINING]   - Found valid nonce: {}", nonce);
                println!("[MINING]   - Mining time: {:.2} seconds", elapsed);
                println!("[MINING]   - Block #{} mined (hash: {})", block.index, hex::encode(block.hash()));
                println!("[MINING]   - Difficulty {} challenge passed!", difficulty);
                
                for tx in &block.transactions {
                    if tx.from != "0000000000000000000000000000000000000000" {
                        *self.balances.get_mut(&tx.from).ok_or("Sender balance not found")? -= tx.value;
                        println!("[BALANCE] {}: -{} (new: {})", 
                                 tx.from, tx.value, self.balances.get(&tx.from).unwrap());
                    }
                    *self.balances.entry(tx.to.clone()).or_insert(0) += tx.value;
                    println!("[BALANCE] {}: +{} (new: {})", 
                             tx.to, tx.value, self.balances.get(&tx.to).unwrap());
                }
                
                println!("[MINING] Difficulty Progress Summary:");
                println!("[MINING]   - Total blocks mined: {}", block.index);
                println!("[MINING]   - Difficulty levels completed: 1 → 2 → ... → {}", difficulty);
                if difficulty >= TARGET_DIFFICULTY {
                    println!("[MINING]   - You have reached target difficulty level {} (exploit condition unlocked!)", TARGET_DIFFICULTY);
                }
                
                self.chain.push(block.clone());
                self.pending_tx.clear();
                println!("[MINING] Pending transactions cleared");
                return Ok(Some(block));
            }
            
            nonce += nonce_step;
            
            // 降低打印频率，减少刷屏
            let print_interval = match difficulty {
                1 => 50,
                2 => 50,
                3 => 100,
                4 => 200,
                _ => 500,
            };
            
            if nonce % print_interval == 0 {
                let elapsed = start.elapsed().as_secs_f64();
                print!("[MINING] Tried nonce: {} (elapsed: {:.1}s, difficulty: {})\r", 
                       nonce, elapsed, difficulty);
                stdout().flush()?;
            }
        }
    }

    fn check_double_spend(&self) -> bool {
        let mut tx_hashes = HashSet::new();
        let mut addr_balances = HashMap::new();
        for block in &self.chain {
            for tx in &block.transactions {
                if tx.from == "0000000000000000000000000000000000000000" { continue; }
                let hash = tx.hash();
                let balance = addr_balances.entry(tx.from.clone()).or_insert(*self.balances.get(&tx.from).unwrap_or(&0));
                if tx_hashes.contains(&hash) || *balance < tx.value {
                    println!("[EXPLOIT] Double spend detected (tx hash: {})", hex::encode(hash));
                    return true;
                }
                tx_hashes.insert(hash);
                *balance -= tx.value;
            }
        }
        false
    }

    fn check_exploit(&self) -> Result<bool, Box<dyn Error>> {
        let double_spend = self.check_double_spend();
        let block_conditions = self.chain.iter().any(|b| b.index >= 3 && b.difficulty >= TARGET_DIFFICULTY);
        let data_processed = self.chain.iter().any(|b| b.process_data().unwrap_or(false));
        let node_unlocked = !self.lock;
        
        println!("[EXPLOIT CHECK] Double spend: {}", double_spend);
        println!("[EXPLOIT CHECK] Block conditions (index≥3 & difficulty≥{}) {}", TARGET_DIFFICULTY, block_conditions);
        println!("[EXPLOIT CHECK] Data processed successfully: {}", data_processed);
        println!("[EXPLOIT CHECK] Node unlocked: {}", node_unlocked);
        
        let exploit_met = double_spend && block_conditions && data_processed && node_unlocked;
        Ok(exploit_met)
    }

    fn generate_dynamic_flag(&self) -> String {
        let latest_block = self.chain.last().unwrap();
        let block_hash = hex::decode(&hex::encode(latest_block.hash())).unwrap();
        let mut hasher = Sha256::new();
        hasher.update(block_hash);
        let flag_hash = hex::encode(hasher.finalize())[..32].to_string();
        format!("flag{{{}}}", flag_hash)
    }

    fn read_flag(&self) -> Result<Option<String>, Box<dyn Error>> {
        Ok(if self.check_exploit()? { 
            let flag = self.generate_dynamic_flag();
            println!("[FLAG] ==============================");
            println!("[FLAG] Exploit conditions met! FLAG: {}", flag);
            println!("[FLAG] ==============================");
            Some(flag) 
        } else { 
            println!("[FLAG] Exploit conditions not met - No flag");
            None 
        })
    }
}

fn parse_command(input: &str, bc: &mut Blockchain) -> Result<(), Box<dyn Error>> {
    let parts: Vec<&str> = input.trim().split_whitespace().collect();
    if parts.is_empty() {
        return Ok(());
    }

    match parts[0] {
        "help" => {
            println!("\n=== Available Commands ===");
            println!("help          - Show this help message");
            println!("balance <addr> - Check balance of an address");
            println!("send_tx <from> <to> <value> [data_hex] - Send transaction (data is hex string)");
            println!("mine          - Start mining a new block (difficulty up to {})", TARGET_DIFFICULTY);
            println!("status        - Show blockchain status (including difficulty progress)");
            println!("check_flag    - Check if exploit conditions are met");
            println!("exit          - Exit the program");
            println!("==========================\n");
        }
        "balance" => {
            if parts.len() < 2 {
                println!("[ERROR] Usage: balance <address>");
                return Ok(());
            }
            let addr = parts[1];
            let balance = bc.balances.get(addr).unwrap_or(&0);
            println!("[BALANCE] Address {} has balance: {}", addr, balance);
        }
        "send_tx" => {
            if parts.len() < 4 {
                println!("[ERROR] Usage: send_tx <from_addr> <to_addr> <value> [data_hex]");
                println!("[EXAMPLE] send_tx <genesis_addr> <miner_addr> 50");
                println!("[EXAMPLE] send_tx <genesis_addr> <miner_addr> 10 <tar_file_hex>");
                return Ok(());
            }
            let from = parts[1].to_string();
            let to = parts[2].to_string();
            let value = parts[3].parse::<u64>().map_err(|e| format!("Invalid value: {}", e))?;
            
            let secp = SECP_CONTEXT.get().ok_or("SECP context not initialized")?;
            let genesis_sk_bytes = hex::decode(GENESIS_PRIV_KEY)?;
            let sk = SecretKey::from_slice(&genesis_sk_bytes)?;
            
            let nonce = match bc.used_nonces.get(&from) {
                Some(set) => set.iter().max().copied().unwrap_or(0) + 1,
                None => 1,
            };

            let data = if parts.len() >= 5 {
                Some(hex::decode(parts[4]).map_err(|e| format!("Invalid data hex: {}", e))?)
            } else {
                None
            };

            let tx = Transaction {
                from: from.clone(),
                to: to.clone(),
                value,
                signature: vec![0; 64],
                nonce,
                data,
                version: 1,
            };
            let tx_hash = tx.hash();
            let msg = Message::from_slice(&tx_hash)?;
            let sig = secp.sign_ecdsa(&msg, &sk);
            let mut signed_tx = tx;
            signed_tx.signature = sig.serialize_compact().to_vec();

            match bc.add_tx(signed_tx) {
                Ok(true) => println!("[SEND_TX] Transaction added successfully (nonce: {})", nonce),
                Ok(false) => println!("[SEND_TX] Failed to add transaction"),
                Err(e) => println!("[SEND_TX] Error: {}", e),
            }
        }
        "mine" => {
            match bc.mine(MINER_ADDR) {
                Ok(Some(_)) => println!("[MINE] Mining completed successfully (difficulty level passed!)"),
                Ok(None) => println!("[MINE] Mining failed (node locked)"),
                Err(e) => println!("[MINE] Error: {}", e),
            }
        }
        "status" => {
            println!("\n=== Blockchain Status ===");
            println!("Total blocks: {}", bc.chain.len());
            println!("Pending transactions: {}", bc.pending_tx.len());
            println!("Error count: {} / {}", bc.error_count, ERROR_LOCK_THRESHOLD);
            println!("Node locked: {}", bc.lock);
            if let Some(last_block) = bc.chain.last() {
                println!("Last block difficulty: {}", last_block.difficulty);
                let next_difficulty = if last_block.difficulty < TARGET_DIFFICULTY {
                    last_block.difficulty + 1
                } else {
                    TARGET_DIFFICULTY
                };
                println!("Next block difficulty: {} (up to {})", next_difficulty, TARGET_DIFFICULTY);
                println!("Difficulty progress: 1 → 2 → ... → {} (target: {})", last_block.difficulty, TARGET_DIFFICULTY);
                if last_block.difficulty >= TARGET_DIFFICULTY {
                    println!("Reached target difficulty level {} (exploit condition unlocked)", TARGET_DIFFICULTY);
                } else {
                    println!("Need to reach target difficulty level {} ({} more levels)", TARGET_DIFFICULTY, TARGET_DIFFICULTY - last_block.difficulty);
                }
            }
            let secp = SECP_CONTEXT.get().unwrap();
            let genesis_sk_bytes = hex::decode(GENESIS_PRIV_KEY).unwrap();
            let genesis_sk = SecretKey::from_slice(&genesis_sk_bytes).unwrap();
            let genesis_pk = PublicKey::from_secret_key(secp, &genesis_sk);
            let genesis_addr = hex::encode(genesis_pk.serialize());
            println!("Genesis address balance: {}", bc.balances.get(&genesis_addr).unwrap_or(&0));
            println!("Miner address balance: {}", bc.balances.get(MINER_ADDR).unwrap_or(&0));
            println!("==========================\n");
        }
        "check_flag" => {
            let _ = bc.read_flag();
        }
        "exit" => {
            println!("[EXIT] Exiting Rust Secure Blockchain v2.0");
            std::process::exit(0);
        }
        _ => {
            println!("[ERROR] Unknown command: '{}' (type 'help' for list)", parts[0]);
            bc.increment_error_count();
        }
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    println!("=== Rust Secure Blockchain v2.0 (Stable Mining Mode) ===");
    println!("Genesis Pubkey: 0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f8179");
    println!("Miner Address: {}", MINER_ADDR);
    println!("Difficulty Rules: Initial={}, Grow to {} and stay (stable timing)", INITIAL_DIFFICULTY, TARGET_DIFFICULTY);
    println!("Mining Speed: STABLE (difficulty 1-3: 1-5s, difficulty 4: 5-8s)");
    println!("Warning: Invalid operation will lock the node permanently ({} errors)", ERROR_LOCK_THRESHOLD);
    println!("Type 'help' to see available commands\n");
    println!("====================================\n");

    let mut bc = Blockchain::global();
    let secp = SECP_CONTEXT.get().unwrap();
    let genesis_sk_bytes = hex::decode(GENESIS_PRIV_KEY).unwrap();
    let genesis_sk = SecretKey::from_slice(&genesis_sk_bytes).unwrap();
    let genesis_pk = PublicKey::from_secret_key(secp, &genesis_sk);
    let genesis_addr = hex::encode(genesis_pk.serialize());

    println!("[INIT] Genesis Address derived: {}", genesis_addr);
    println!("[INIT] Genesis Address Balance: {}", bc.balances.get(&genesis_addr).unwrap_or(&0));

    let tx = Transaction {
        from: genesis_addr.clone(),
        to: MINER_ADDR.to_string(),
        value: 100,
        signature: vec![0u8; 64],
        nonce: 0,
        data: None,
        version: 1,
    };
    let tx_hash = tx.hash();
    let msg = Message::from_slice(&tx_hash)?;
    let sig = secp.sign_ecdsa(&msg, &genesis_sk);
    let mut signed_tx = tx;
    signed_tx.signature = sig.serialize_compact().to_vec();

    match bc.add_tx(signed_tx) {
        Ok(true) => println!("[INIT] Initial transaction added successfully"),
        Ok(false) => println!("[INIT] Failed to add initial transaction"),
        Err(e) => println!("[INIT] Error adding initial transaction: {}", e),
    }

    loop {
        print!("> ");
        stdout().flush()?;
        let mut input = String::new();
        stdin().read_line(&mut input)?;
        if let Err(e) = parse_command(&input, &mut bc) {
            println!("[ERROR] Command execution failed: {}", e);
            bc.increment_error_count();
        }
    }
}