// Copyright (c) 2026 zkSecurity. Apache-2.0.
// Diagnostic access to the unchanged production accumulated-weight kernel.
use super::*;
pub fn add(acc: &mut [F192], values: &[F192], scalar: F192) { add_scaled(acc, values, scalar); }

pub fn round(f: &[F192], b: &[F192]) -> [F192; 2] { let (msg, _) = round_msg_lsb::<false>(f,b); [msg.u_0,msg.u_2] }
