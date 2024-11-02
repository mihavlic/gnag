
use gnag_runtime::lexer::*;
use gnag_runtime::parser::*;
use gnag_runtime::*;
pub fn File(p: &mut Parser) -> bool {
    'b0: {
        'b1: {
            let checkpoint = p.save_state();
            'b2: {
                if !Expression(p) {
                    break 'b2;
                }
                p.close_span(NodeKind::File);
                return true;
            }
            p.restore_state(checkpoint);
        }
        return false;
    }
}
pub fn Expression(p: &mut Parser) -> bool {
    'b0: {
        'b1: {
            let checkpoint = p.save_state();
            'b2: {
                'b3: {
                    'b4: {
                        let checkpoint = p.save_state();
                        'b5: {
                            if !l.token(nodeKind::Number) {
                                break 'b5;
                            }
                            p.close_span(NodeKind::Atom);
                            break 'b3;
                        }
                        p.restore_state(checkpoint);
                    }
                    break 'b2;
                }
                'b6: loop {
                    'b7: {
                        'b8: {
                            let checkpoint = p.save_state();
                            'b9: {
                                if !precedence < 1 {
                                    break 'b9;
                                }
                                if !l.token(nodeKind::Plus) {
                                    break 'b9;
                                }
                                Expression(p);
                                p.close_span(NodeKind::Add);
                                continue 'b6;
                            }
                            p.restore_state(checkpoint);
                        }
                        'b10: {
                            let checkpoint = p.save_state();
                            'b11: {
                                if !precedence < 2 {
                                    break 'b11;
                                }
                                if !l.token(nodeKind::Star) {
                                    break 'b11;
                                }
                                Expression(p);
                                p.close_span(NodeKind::Mul);
                                continue 'b6;
                            }
                            p.restore_state(checkpoint);
                        }
                        break 'b6;
                    }
                }
                return true;
            }
            p.restore_state(checkpoint);
        }
        return false;
    }
}
pub fn Lexer(p: &mut Parser) -> bool {
    'b0: {
        'b1: {
            let checkpoint = p.save_state();
            'b2: {
                if !l.ascii_class(CharacterClass::TODO) {
                    break 'b2;
                }
                'b3: {
                    match l.ascii_class(CharacterClass::TODO) {
                        true => continue 'b3,
                        false => break 'b3,
                    }
                }
                return Some(NodeKind::Space);
            }
            p.restore_state(checkpoint);
        }
        'b4: {
            let checkpoint = p.save_state();
            'b5: {
                if !l.bytes(b"+") {
                    break 'b5;
                }
                return Some(NodeKind::Plus);
            }
            p.restore_state(checkpoint);
        }
        'b6: {
            let checkpoint = p.save_state();
            'b7: {
                if !l.bytes(b"*") {
                    break 'b7;
                }
                return Some(NodeKind::Star);
            }
            p.restore_state(checkpoint);
        }
        'b8: {
            let checkpoint = p.save_state();
            'b9: {
                if !l.ascii_class(CharacterClass::TODO) {
                    break 'b9;
                }
                'b10: {
                    match l.ascii_class(CharacterClass::TODO) {
                        true => continue 'b10,
                        false => break 'b10,
                    }
                }
                return Some(NodeKind::Number);
            }
            p.restore_state(checkpoint);
        }
        'b11: {
            let checkpoint = p.save_state();
            'b12: {
                if !p.any() {
                    break 'b12;
                }
                return Some(NodeKind::Error);
            }
            p.restore_state(checkpoint);
        }
        return None;
    }
}
