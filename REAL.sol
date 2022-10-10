// SPDX-License-Identifier: MIT

// File: @openzeppelin/contracts/utils/math/SafeMath.sol

// OpenZeppelin Contracts (last updated v4.6.0) (utils/math/SafeMath.sol)

pragma solidity ^0.8.0;

// CAUTION
// This version of SafeMath should only be used with Solidity 0.8 or later,
// because it relies on the compiler's built in overflow checks.

/**
 * @dev Wrappers over Solidity's arithmetic operations.
 *
 * NOTE: `SafeMath` is generally not needed starting with Solidity 0.8, since the compiler
 * now has built in overflow checking.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryAdd(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            uint256 c = a + b;
            if (c < a) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b > a) return (false, 0);
            return (true, a - b);
        }
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
            // benefit is lost if 'b' is also tested.
            // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
            if (a == 0) return (true, 0);
            uint256 c = a * b;
            if (c / a != b) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryDiv(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a / b);
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a % b);
        }
    }

    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return a - b;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * b;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator.
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return a % b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {trySub}.
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b <= a, errorMessage);
            return a - b;
        }
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a / b;
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting with custom message when dividing by zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryMod}.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a % b;
        }
    }
}

// File: @openzeppelin/contracts/token/ERC20/IERC20.sol

// OpenZeppelin Contracts (last updated v4.6.0) (token/ERC20/IERC20.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);
}

// File: @openzeppelin/contracts/utils/Context.sol

// OpenZeppelin Contracts v4.4.1 (utils/Context.sol)

pragma solidity ^0.8.0;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

// File: @openzeppelin/contracts/security/Pausable.sol

// OpenZeppelin Contracts (last updated v4.7.0) (security/Pausable.sol)

pragma solidity ^0.8.0;

/**
 * @dev Contract module which allows children to implement an emergency stop
 * mechanism that can be triggered by an authorized account.
 *
 * This module is used through inheritance. It will make available the
 * modifiers `whenNotPaused` and `whenPaused`, which can be applied to
 * the functions of your contract. Note that they will not be pausable by
 * simply including this module, only once the modifiers are put in place.
 */
abstract contract Pausable is Context {
    /**
     * @dev Emitted when the pause is triggered by `account`.
     */
    event Paused(address account);

    /**
     * @dev Emitted when the pause is lifted by `account`.
     */
    event Unpaused(address account);

    bool private _paused;

    /**
     * @dev Initializes the contract in unpaused state.
     */
    constructor() {
        _paused = false;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is not paused.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    modifier whenNotPaused() {
        _requireNotPaused();
        _;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is paused.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    modifier whenPaused() {
        _requirePaused();
        _;
    }

    /**
     * @dev Returns true if the contract is paused, and false otherwise.
     */
    function paused() public view virtual returns (bool) {
        return _paused;
    }

    /**
     * @dev Throws if the contract is paused.
     */
    function _requireNotPaused() internal view virtual {
        require(!paused(), "Pausable: paused");
    }

    /**
     * @dev Throws if the contract is not paused.
     */
    function _requirePaused() internal view virtual {
        require(paused(), "Pausable: not paused");
    }

    /**
     * @dev Triggers stopped state.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    function _pause() internal virtual whenNotPaused {
        _paused = true;
        emit Paused(_msgSender());
    }

    /**
     * @dev Returns to normal state.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    function _unpause() internal virtual whenPaused {
        _paused = false;
        emit Unpaused(_msgSender());
    }
}

// File: @openzeppelin/contracts/access/Ownable.sol

// OpenZeppelin Contracts (last updated v4.7.0) (access/Ownable.sol)

pragma solidity ^0.8.0;

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _transferOwnership(_msgSender());
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

// File: @openzeppelin/contracts/utils/Address.sol

// OpenZeppelin Contracts (last updated v4.7.0) (utils/Address.sol)

pragma solidity ^0.8.0;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verifies that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly
                /// @solidity memory-safe-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

// File: contracts/interface/IVanswapRouter02.sol

pragma solidity >= 0.8.0;

interface IVanswapRouter02 {
    function factory() external view returns (address);
    function WVS() external pure returns (address);

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint amountADesired,
        uint amountBDesired,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB, uint liquidity);
    function addLiquidityVS(
        address token,
        uint amountTokenDesired,
        uint amountTokenMin,
        uint amountVSMin,
        address to,
        uint deadline
    ) external payable returns (uint amountToken, uint amountVS, uint liquidity);
    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityVS(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountVSMin,
        address to,
        uint deadline
    ) external returns (uint amountToken, uint amountVS);
    function removeLiquidityWithPermit(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountA, uint amountB);
    function removeLiquidityVSWithPermit(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountVSMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountToken, uint amountVS);
    function swapExactTokensForTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapTokensForExactTokens(
        uint amountOut,
        uint amountInMax,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);
    function swapExactVSForTokens(uint amountOutMin, address[] calldata path, address to, uint deadline)
        external
        payable
        returns (uint[] memory amounts);
    function swapTokensForExactVS(uint amountOut, uint amountInMax, address[] calldata path, address to, uint deadline)
        external
        returns (uint[] memory amounts);
    function swapExactTokensForVS(uint amountIn, uint amountOutMin, address[] calldata path, address to, uint deadline)
        external
        returns (uint[] memory amounts);
    function swapVSForExactTokens(uint amountOut, address[] calldata path, address to, uint deadline)
        external
        payable
        returns (uint[] memory amounts);

    function quote(uint amountA, uint reserveA, uint reserveB) external pure returns (uint amountB);
    function getAmountOut(uint amountIn, uint reserveIn, uint reserveOut) external pure returns (uint amountOut);
    function getAmountIn(uint amountOut, uint reserveIn, uint reserveOut) external pure returns (uint amountIn);
    function getAmountsOut(uint amountIn, address[] calldata path) external view returns (uint[] memory amounts);
    function getAmountsIn(uint amountOut, address[] calldata path) external view returns (uint[] memory amounts);

    function removeLiquidityVSSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountVSMin,
        address to,
        uint deadline
    ) external returns (uint amountVS);
    function removeLiquidityVSWithPermitSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountVSMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountVS);

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
    function swapExactVSForTokensSupportingFeeOnTransferTokens(
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external payable;
    function swapExactTokensForVSSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
}
// File: contracts/interface/IVanswapFactory.sol

pragma solidity >= 0.8.0;

interface IVanswapFactory {
    event PairCreated(address indexed token0, address indexed token1, address pair, uint);

    function feeTo() external view returns (address);
    function feeToSetter() external view returns (address);

    function getPair(address tokenA, address tokenB) external view returns (address pair);
    function allPairs(uint) external view returns (address pair);
    function allPairsLength() external view returns (uint);

    function createPair(address tokenA, address tokenB) external returns (address pair);

    function setFeeTo(address) external;
    function setFeeToSetter(address) external;
}
// File: contracts/utils/VanswapLibrary.sol

pragma solidity ^0.8.0;

library VanswapLibrary {
    function calculateAddr(address pair,address tokenA, address tokenB) internal pure returns(address predictedAddress){
            (address token0, address token1) = tokenA < tokenB ? (tokenA, tokenB) : (tokenB, tokenA);
            bytes32 salt = keccak256(abi.encodePacked(token0, token1));
            predictedAddress = address(uint160(uint(keccak256(abi.encodePacked(
                bytes1(0x46),
                pair,
                salt,
                hex'700ac9ac48960f6c4b996b52a656e59f57d6071d19134206a8fa05933d9e0ca9'
            )))));
        }
}

// File: contracts/Real.sol

pragma solidity >=0.8.0;

/**
    88888888ba  88888888888        db        88           
    88      "8b 88                d88b       88           
    88      ,8P 88               d8'`8b      88           
    88aaaaaa8P' 88aaaaa         d8'  `8b     88           
    88""""88'   88"""""        d8YaaaaY8b    88           
    88    `8b   88            d8""""""""8b   88           
    88     `8b  88           d8'        `8b  88           
    88      `8b 88888888888 d8'          `8b 88888888888  
 */
contract Real is IERC20, Ownable, Pausable {
    using SafeMath for uint256;
    using Address for address;

    string private _name = "REAL";
    string private _symbol = "REAL";
    uint8 private _decimals = 9;

    mapping (address => uint256) private _rOwned;
    mapping (address => uint256) private _tOwned;
    mapping (address => mapping (address => uint256)) private _allowances;
    mapping (address => bool) private _isBlackList;

    mapping (address => bool) private _isExcludedFromFee;
    mapping (address => bool) private _isExcluded;
    address[] private _excluded;

    uint256 private constant MAX = ~uint256(0);
    uint256 private _tTotal = 100_000_000 * 10 ** _decimals;
    uint256 private _rTotal = (MAX - (MAX % _tTotal)); 

    uint256 private _tFeeTotal;  

    uint256 public _taxFee = 0;         
    uint256 private _previousTaxFee = _taxFee;

    uint256 public _liquidityFee = 5;       
    uint256 private _previousLiquidityFee = _liquidityFee;

    uint256 public _rebateFee = 3; 

    uint256 private _previousRebateFee = _rebateFee;
    address public _rebateAddr = 0xB451D988Aa27DcB3b336d176165887B911836D86; 

    uint256 public _buyBurningFee = 2; 
    uint256 private _previousBuyBurningFee = _buyBurningFee;

    uint256 public _sellBurningFee = 5; 
    uint256 private _previousSellBurningFee = _sellBurningFee;
    address public _burnAddr = 0x000000000000000000000000000000000000dEaD; 

    uint256 public _safeFee = 3; 
    uint256 private _previousSafeFee = _safeFee;
    address public _safeAddr = 0x511330f7AD22bB4daB394280D967b7634c8e2Fa7; 

    uint256 public _poolFee = 5; 
    uint256 private _previousPoolFee;
    address public _poolAddr = 0xfF41aA96C9859cc2889701Cf3A523bE89d625bC6; 

    uint256 public _sellBonusFee = 2; 
    uint256 private _previousSellBonusFee = _sellBonusFee;

    IVanswapRouter02 public immutable vanswapV2Router;
    mapping (address => bool) public tollStation; 
    address public immutable vanswapV2Pair;

    enum TxType {normal, buy, sell}
    TxType private _currentTxType; 

    bool inSwapAndLiquify; 
    bool public swapAndLiquifyEnabled = true;  

    uint256 public _maxTxAmount = MAX;    
    uint256 private numTokensSellToAddToLiquidity = 100 *  10 ** _decimals;          
    uint256 public _lastAddToLiquidityTime = 0;  
    uint64 public _addToLiquidityTimeInterval = 30 minutes; 

    struct TValues {
        uint256 tAmount;
        uint256 tTransferAmount;
        uint256 tFee;
        uint256 tLiquidity;
        uint256 tRebate;
        uint256 tBuyBurning;
        uint256 tSafe;
        uint256 tSellBurning;
        uint256 tPool;
        uint256 tSellBonus;
    }

    struct RValues {
        uint256 rAmount;
        uint256 rTransferAmount;
        uint256 rFee;
        uint256 rLiquidity;
        uint256 rRebate;
        uint256 rBuyBurning;
        uint256 rSafe;
        uint256 rSellBurning;
        uint256 rPool;
        uint256 rSellBonus;
    }

    event MinTokensBeforeSwapUpdated(uint256 minTokensBeforeSwap);
    event SwapAndLiquifyEnabledUpdated(bool enabled);
    event SwapAndLiquify(
        uint256 tokensSwapped,
        uint256 ethReceived,
        uint256 tokensIntoLiqudity
    );

    modifier lockTheSwap {
        inSwapAndLiquify = true;
        _;
        inSwapAndLiquify = false;
    }

    constructor(address vanswapRouter, address ow) {
        _rOwned[ow] = _rTotal;

        IVanswapRouter02 _vanswapV2Router = IVanswapRouter02(vanswapRouter);

        address p = VanswapLibrary.calculateAddr(_vanswapV2Router.factory(), address(this), _vanswapV2Router.WVS());
        vanswapV2Pair = p;

        tollStation[p] = true;

        vanswapV2Router = _vanswapV2Router;

        _isExcludedFromFee[ow] = true;
        _isExcludedFromFee[address(this)] = true; 
        _isExcludedFromFee[_safeAddr] = true;
        _isExcludedFromFee[_poolAddr] = true;
        _isExcludedFromFee[_rebateAddr] = true;

        _isExcluded[_poolAddr] = true;
        _isExcluded[_burnAddr] = true;
        _isExcluded[_safeAddr] = true;
        _isExcluded[p] = true;
        _excluded.push(_poolAddr);
        _excluded.push(_burnAddr);
        _excluded.push(_safeAddr);
        _excluded.push(p);

        _approve(address(this), vanswapRouter, MAX);

        emit Transfer(address(0), ow, _tTotal);
    }

    function name() public view returns (string memory) {
        return _name;
    }

    function symbol() public view returns (string memory) {
        return _symbol;
    }

    function decimals() public view returns (uint8) {
        return _decimals;
    }

    function totalSupply() public view override returns (uint256) {
        return _tTotal;
    }

    function balanceOf(address account) public view override returns (uint256) {
        if (_isExcluded[account]) return _tOwned[account];
        return tokenFromReflection(_rOwned[account]);
    }

    function transfer(address recipient, uint256 amount) public override whenNotPaused returns (bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    function allowance(address ow, address spender) public view override returns (uint256) {
        return _allowances[ow][spender];
    }

    function approve(address spender, uint256 amount) public override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    function transferFrom(address sender, address recipient, uint256 amount) public override whenNotPaused returns (bool) {
        _transfer(sender, recipient, amount);
        if ( _allowances[sender][_msgSender()] != MAX) {
            _approve(sender, _msgSender(), _allowances[sender][_msgSender()].sub(amount, "ERC20: transfer amount exceeds allowance"));
        }
        return true;
    }

    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        if (_allowances[_msgSender()][spender] != MAX) {
            _approve(_msgSender(), spender, _allowances[_msgSender()][spender].add(addedValue));
        }
        return true;
    }

    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        if (_allowances[_msgSender()][spender] != MAX) {
            _approve(_msgSender(), spender, _allowances[_msgSender()][spender].sub(subtractedValue, "ERC20: decreased allowance below zero"));
        }
        return true;
    }

    function pause() public onlyOwner whenNotPaused {
        super._pause();
    }

    function unPause() public onlyOwner whenPaused {
        super._unpause();
    }

    function isExcludedFromReward(address account) public view returns (bool) {
        return _isExcluded[account];
    }

    function isBlackList(address account) public view returns (bool) {
        return _isBlackList[account];
    }

    function totalFees() public view returns (uint256) {
        return _tFeeTotal;
    }

    function deliver(uint256 tAmount) public {
        address sender = _msgSender();
        require(!_isExcluded[sender], "Excluded addresses cannot call this function");
        uint256 rAmount = _getValue(tAmount);
        _rOwned[sender] = _rOwned[sender].sub(rAmount);
        _rTotal = _rTotal.sub(rAmount);
        _tFeeTotal = _tFeeTotal.add(tAmount);
    }

    function reflectionFromToken(uint256 tAmount, bool deductTransferFee) public view returns(uint256) {
        require(tAmount <= _tTotal, "Amount must be less than supply");
        if (!deductTransferFee) {
            uint256 rAmount= _getValue(tAmount);
            return rAmount;
        } else {
            (RValues memory r,) = _getValues(tAmount);
            return r.rTransferAmount;
        }
    }

    function setTollStationAddress(address tollStationAddress) external onlyOwner {
        tollStation[tollStationAddress] = true;
    }

    function removeTollStationAdress(address tollStationAddress) external onlyOwner {
        if (tollStation[tollStationAddress]) {
            tollStation[tollStationAddress] = false;
        }
    }

    function tokenFromReflection(uint256 rAmount) private view returns(uint256) {
        require(rAmount <= _rTotal, "Amount must be less than total reflections");
        uint256 currentRate =  _getRate();
        return rAmount.div(currentRate);
    }

    function excludeFromReward(address account) public onlyOwner {
        require(!_isExcluded[account], "Account is already excluded");
        if(_rOwned[account] > 0) {
            _tOwned[account] = tokenFromReflection(_rOwned[account]);
        }
        _isExcluded[account] = true;
        _excluded.push(account);
    }

    function includeInReward(address account) external onlyOwner {
        require(_isExcluded[account], "Account is already excluded");
        for (uint256 i = 0; i < _excluded.length; i++) {
            if (_excluded[i] == account) {
                _excluded[i] = _excluded[_excluded.length - 1];
                _tOwned[account] = 0;
                _isExcluded[account] = false;
                _excluded.pop();
                break;
            }
        }
    }

    function setBlackList(address account) external onlyOwner {
        require(!_isBlackList[account], "Account is already blacklist");
        _isBlackList[account] = true;
    }

    function removeBlackList(address account) external onlyOwner {
        require(_isBlackList[account], "Account is not in blacklist");
        _isBlackList[account] = false;
    }

    function excludeFromFee(address account) public onlyOwner {
        _isExcludedFromFee[account] = true;
    }

    function includeInFee(address account) public onlyOwner {
        _isExcludedFromFee[account] = false;
    }

    function setTaxFeePercent(uint256 taxFee) external onlyOwner {
        _taxFee = taxFee;
    }

    function setRebateFee(uint256 rebateFee) external onlyOwner {
        _rebateFee = rebateFee;
    }

    function setRebateAddr(address rebateAddr) external onlyOwner {
        _rebateAddr = rebateAddr;
    }

    function setBuyBurningFee(uint256 buyBurningFee) external onlyOwner {
        _buyBurningFee = buyBurningFee;
    }

    function setSellBurningFee(uint256 sellBurningFee) external onlyOwner {
        _sellBonusFee = sellBurningFee;
    }

    function setBurnAddr(address burnAddr) external onlyOwner{
        _burnAddr = burnAddr;
    }

    function setSafeFee(uint256 safeFee) external onlyOwner {
        _safeFee = safeFee;
    }

    function setSafeAddr(address safeAddr) external onlyOwner {
        _safeAddr = safeAddr;
    }

    function setLiquidityFeePercent(uint256 liquidityFee) external onlyOwner {
        _liquidityFee = liquidityFee;
    }

    function setPoolFee(uint256 poolFee) external onlyOwner {
        _poolFee = poolFee;
    }

   function setPoolAddr(address poolAddr) external onlyOwner {
       _poolAddr = poolAddr;
   }

    function setSellBonusFee(uint256 sellBonusFee) external onlyOwner {
        _sellBonusFee = sellBonusFee;
    }

    function setMaxTxPercent(uint256 maxTxPercent) external onlyOwner {
        _maxTxAmount = _tTotal.mul(maxTxPercent).div(
            100
        );
    }

    function setMaxTxAmount(uint256 maxTxAmount) external onlyOwner {
        _maxTxAmount = maxTxAmount;
    }

    function setAddToLiquidityTimeInterval(uint64 intervalMinute) external onlyOwner {
        _addToLiquidityTimeInterval = intervalMinute * 1 minutes;
    }

    function setSwapAndLiquifyEnabled(bool _enabled) public onlyOwner {
        swapAndLiquifyEnabled = _enabled;
        emit SwapAndLiquifyEnabledUpdated(_enabled);
    }

    receive() external payable {}

    function _getValue(uint256 tamount) private view returns (uint256 ramount) {
        return tamount.mul(_getRate());
    } 

    function _getValues(uint256 tAmount) private view returns (RValues memory, TValues memory) {
       TValues memory tValues= _getTValues(tAmount);

        RValues memory rValues = _getRValues(tValues, _getRate());
        return (rValues, tValues);
    }

    function _getTValues(uint256 tAmount) private view returns (TValues memory v) {
        TValues memory t = TValues({
            tTransferAmount: 0,
            tAmount: tAmount,
            tFee:  calculateTaxFee(tAmount),
            tLiquidity: calculateLiquidityFee(tAmount),
            tRebate: calculateRebateFee(tAmount),
            tBuyBurning: calculateBuyBurningFee(tAmount),
            tSafe: calculateSafeFee(tAmount),
            tSellBurning: calculateSellBurningFee(tAmount),
            tPool: calculatePoolFee(tAmount),
            tSellBonus: calculateSellBonusFee(tAmount)
        });

        t.tTransferAmount = tAmount.sub(t.tFee).sub(t.tLiquidity);
        t.tTransferAmount = t.tTransferAmount.sub(t.tRebate).sub(t.tBuyBurning).sub(t.tSafe);
        t.tTransferAmount = t.tTransferAmount.sub(t.tSellBurning).sub(t.tPool).sub(t.tSellBonus);

        return t;
    }

    function _getRValues(TValues memory t, uint256 currentRate) private view returns (RValues memory) {
        uint256 rAmount = _getValue(t.tAmount);
        RValues memory r = RValues({
            rTransferAmount: 0,
            rAmount: rAmount,
            rFee: t.tFee.mul(currentRate),
            rLiquidity: t.tLiquidity.mul(currentRate),
            rRebate: t.tRebate.mul(currentRate),
            rBuyBurning : t.tBuyBurning.mul(currentRate),
            rSafe: t.tSafe.mul(currentRate),
            rSellBurning: t.tSellBurning.mul(currentRate),
            rPool: t.tPool.mul(currentRate),
            rSellBonus: t.tSellBonus.mul(currentRate)
        });

        r.rTransferAmount = rAmount.sub(r.rFee).sub(r.rRebate).sub(r.rBuyBurning);
        r.rTransferAmount = r.rTransferAmount.sub(r.rSafe).sub(r.rSellBurning).sub(r.rLiquidity);
        r.rTransferAmount = r.rTransferAmount.sub(r.rPool).sub(r.rSellBonus);

        return r;
    }

    function _getRate() private view returns(uint256) {
        (uint256 rSupply, uint256 tSupply) = _getCurrentSupply();
        return rSupply.div(tSupply);
    }

    function _getCurrentSupply() private view returns(uint256, uint256) {
        uint256 rSupply = _rTotal;
        uint256 tSupply = _tTotal;      
        for (uint256 i = 0; i < _excluded.length; i++) {
            if (_rOwned[_excluded[i]] > rSupply || _tOwned[_excluded[i]] > tSupply) return (_rTotal, _tTotal); 
            rSupply = rSupply.sub(_rOwned[_excluded[i]]);
            tSupply = tSupply.sub(_tOwned[_excluded[i]]);
        }
        if (rSupply < _rTotal.div(_tTotal)) return (_rTotal, _tTotal);
        return (rSupply, tSupply);
    }

    function _reflectFee(uint256 rFee, uint256 tFee) private {
        _rTotal = _rTotal.sub(rFee);
        _tFeeTotal = _tFeeTotal.add(tFee);
    }

    function _takeSellBonusFee(uint256 tSellBonusFee) private {
        if (tSellBonusFee == 0) return;

        uint256 currentRate =  _getRate();
        uint256 rSellBonusFee = tSellBonusFee.mul(currentRate);

        _rTotal = _rTotal.sub(rSellBonusFee);
    }

    function _takeLiquidity(uint256 tLiquidity) private {
        if (tLiquidity == 0) return;

        uint256 currentRate =  _getRate();
        uint256 rLiquidity = tLiquidity.mul(currentRate);
        _rOwned[address(this)] = _rOwned[address(this)].add(rLiquidity);

        if(_isExcluded[address(this)])
            _tOwned[address(this)] = _tOwned[address(this)].add(tLiquidity);
    }

    function _takeRebateFee(uint256 tRebateFee) private {
        if (tRebateFee == 0) return;

        uint256 currentRate = _getRate();
        uint256 rRebateFee = tRebateFee.mul(currentRate);
        _rOwned[_rebateAddr] = _rOwned[_rebateAddr].add(rRebateFee);

        if (_isExcluded[_rebateAddr])
            _tOwned[_rebateAddr] = _tOwned[_rebateAddr].add(tRebateFee);
    }

    function _toBurn(uint256 tBurnFee) private {
        if (tBurnFee == 0) return;

        uint256 currentRate = _getRate();
        uint256 rBurnFee = tBurnFee.mul(currentRate);
        _rOwned[_burnAddr] = _rOwned[_burnAddr].add(rBurnFee);

        if (_isExcluded[_burnAddr])
            _tOwned[_burnAddr] = _tOwned[_burnAddr].add(tBurnFee);
    }

    function _toSafe(uint256 tSafeFee) private {
        if (tSafeFee == 0) return;
        uint256 currentRate = _getRate();
        uint256 rSafeFee = tSafeFee.mul(currentRate);
        _rOwned[_safeAddr] = _rOwned[_safeAddr].add(rSafeFee);

        if (_isExcluded[_safeAddr])
            _tOwned[_safeAddr] = _tOwned[_safeAddr].add(tSafeFee);
    }

    function _toPool(uint256 tPoolFee) private {
        if (tPoolFee == 0) return;

        uint256 currentRate = _getRate();
        uint256 rPoolFee = tPoolFee.mul(currentRate);
        _rOwned[_poolAddr] = _rOwned[_poolAddr].add(rPoolFee);

        if (_isExcluded[_poolAddr])
            _tOwned[_poolAddr] = _tOwned[_poolAddr].add(tPoolFee);
    }

    function calculateTaxFee(uint256 _amount) private view returns (uint256) {

        if (_currentTxType != TxType.normal) return 0;

        return _amount.mul(_taxFee).div(
            100
        );
    }

    function calculateLiquidityFee(uint256 _amount) private view returns (uint256) {

        if (_currentTxType != TxType.buy) return 0;

        return _amount.mul(_liquidityFee).div(
            100
        );
    }

    function calculateRebateFee(uint256 _amount) private view returns (uint256) {
        if (_currentTxType != TxType.buy) return 0;

        return _amount.mul(_rebateFee).div(
            100
        );
    }

    function calculateBuyBurningFee(uint256 _amount) private view returns (uint256) {
        if (_currentTxType != TxType.buy) return 0;

        return _amount.mul(_buyBurningFee).div(
            100
        );
    }

    function calculateSellBurningFee(uint256 _amount) private view returns (uint256) {
        if (_currentTxType != TxType.sell) return 0;

        return _amount.mul(_sellBurningFee).div(
            100
        );
    }

    function calculateSafeFee(uint256 _amount) private view returns (uint256) {
        if (_currentTxType != TxType.sell) return 0;

        return _amount.mul(_safeFee).div(
            100
        );
    }

    function calculatePoolFee(uint256 _amount) private view returns (uint256) {
        if (_currentTxType != TxType.sell) return 0;

        return _amount.mul(_poolFee).div(
            100
        );
    }

    function calculateSellBonusFee(uint256 _amount) private view returns (uint256) {
        if (_currentTxType != TxType.sell) return 0;

        return _amount.mul(_sellBonusFee).div(
            100
        );
    }

    function removeAllFee() private {

        _previousTaxFee = _taxFee;
        _previousLiquidityFee = _liquidityFee;
        _previousRebateFee = _rebateFee;
        _previousBuyBurningFee = _buyBurningFee;
        _previousSellBurningFee = _sellBurningFee;
        _previousSafeFee = _safeFee;
        _previousPoolFee = _poolFee;
        _previousSellBonusFee = _sellBonusFee;

        _taxFee = 0;
        _liquidityFee = 0;
        _rebateFee = 0;
        _buyBurningFee = 0;
        _sellBurningFee = 0;
        _safeFee = 0;
        _poolFee = 0;
        _sellBonusFee = 0;
    }

    function restoreAllFee() private {

        _taxFee = _previousTaxFee;
        _liquidityFee = _previousLiquidityFee;
        _rebateFee = _previousRebateFee;
        _buyBurningFee = _previousBuyBurningFee;
        _sellBurningFee = _previousSellBurningFee;
        _safeFee = _previousSafeFee;
        _poolFee = _previousPoolFee;
        _sellBonusFee = _previousSellBonusFee;
    }

    function isExcludedFromFee(address account) public view returns(bool) {
        return _isExcludedFromFee[account];
    }

    function _approve(address ow, address spender, uint256 amount) private {
        require(ow != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[ow][spender] = amount;
        emit Approval(ow, spender, amount);
    }

    function _transfer(
        address from,
        address to,
        uint256 amount
    ) private {
        require(from != address(0), "ERC20: transfer from the zero address");
        require(to != address(0), "ERC20: transfer to the zero address");
        require(amount > 0, "Transfer amount must be greater than zero");
        require(!_isBlackList[from], "Blacklisted users are not allowed to trade");
        require(!_isBlackList[to], "Blacklisted users are not allowed to trade");

        if(from != owner() && to != owner())
            require(amount <= _maxTxAmount, "Transfer amount exceeds the maxTxAmount.");

        uint256 contractTokenBalance = balanceOf(address(this));

        if(contractTokenBalance >= _maxTxAmount)
        {
            contractTokenBalance = _maxTxAmount;
        }

        bool overMinTokenBalance = contractTokenBalance >= numTokensSellToAddToLiquidity;
        bool overSwapTime = (block.timestamp - _lastAddToLiquidityTime) >= _addToLiquidityTimeInterval;

        if (
            (overMinTokenBalance && overSwapTime) &&
            !inSwapAndLiquify &&
            from != vanswapV2Pair &&
            swapAndLiquifyEnabled
        ) {
            contractTokenBalance = numTokensSellToAddToLiquidity;

            swapAndLiquify(contractTokenBalance);
        }

        bool takeFee = true;

        if(_isExcludedFromFee[from] || _isExcludedFromFee[to]){
            takeFee = false;
        }

        if (takeFee) {
            setTxType(from, to);
        }

        _tokenTransfer(from,to,amount,takeFee);
    }

    function swapAndLiquify(uint256 contractTokenBalance) private lockTheSwap {
        _lastAddToLiquidityTime = block.timestamp;

        uint256 half = contractTokenBalance.div(2);
        uint256 otherHalf = contractTokenBalance.sub(half);

        uint256 initialBalance = address(this).balance;

        swapTokensForEth(half); 

        uint256 newBalance = address(this).balance.sub(initialBalance);

        addLiquidity(otherHalf, newBalance);

        emit SwapAndLiquify(half, newBalance, otherHalf);
    }

    function swapTokensForEth(uint256 tokenAmount) private {

        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = vanswapV2Router.WVS();

        vanswapV2Router.swapExactTokensForVSSupportingFeeOnTransferTokens(
            tokenAmount,
            0, 
            path,
            address(this),
            block.timestamp
        );
    }

    function addLiquidity(uint256 tokenAmount, uint256 ethAmount) private {

        vanswapV2Router.addLiquidityVS{value: ethAmount}(
            address(this),
            tokenAmount,
            0, 
            0, 
            owner(),
            block.timestamp
        );
    }

    function setTxType(address from, address to) private {
        if (tollStation[from]) {
            _currentTxType = TxType.buy;
        } else if (tollStation[to]) {
            _currentTxType = TxType.sell;
        } else {
            _currentTxType = TxType.normal;
        }
    }

    function _tokenTransfer(address sender, address recipient, uint256 amount,bool takeFee) private {

        if (_isExcluded[sender] && !_isExcluded[recipient]) {
            _transferFromExcluded(sender, recipient, amount, takeFee);   
        } else if (!_isExcluded[sender] && _isExcluded[recipient]) {
            _transferToExcluded(sender, recipient, amount, takeFee);     

        } else if (_isExcluded[sender] && _isExcluded[recipient]) {
            _transferBothExcluded(sender, recipient, amount, takeFee); 
        } else {
            _transferStandard(sender, recipient, amount, takeFee); 
        }

    }

    function _transferStandard(address sender, address recipient, uint256 tAmount, bool takeFee) private {
        if (!takeFee) {
            uint256 rAmount = _getValue(tAmount);
            _rOwned[sender] = _rOwned[sender].sub(rAmount);
            _rOwned[recipient] = _rOwned[recipient].add(rAmount);
            emit Transfer(sender, recipient, tAmount);
        } else {
            (RValues memory r, TValues memory t) = _getValues(tAmount);
            _rOwned[sender] = _rOwned[sender].sub(r.rAmount);
            _rOwned[recipient] = _rOwned[recipient].add(r.rTransferAmount);

            _takeLiquidity(t.tLiquidity);
            _reflectFee(r.rFee, t.tFee);
            _takeRebateFee(t.tRebate);
            _toBurn(t.tBuyBurning);
            _toSafe(t.tSafe);
            _toBurn(t.tSellBurning);
            _toPool(t.tPool);
            _takeSellBonusFee(t.tSellBonus);

            emit Transfer(sender, recipient, t.tTransferAmount);
        }
    }

    function _transferBothExcluded(address sender, address recipient, uint256 tAmount, bool takeFee) private {
        if (!takeFee) {
            uint256 rAmount = _getValue(tAmount);
            _tOwned[sender] = _tOwned[sender].sub(tAmount);
            _rOwned[sender] = _rOwned[sender].sub(rAmount);
            _tOwned[recipient] = _tOwned[recipient].add(tAmount);
            _rOwned[recipient] = _rOwned[recipient].add(rAmount);    
            emit Transfer(sender, recipient, tAmount);
        } else {
            (RValues memory r, TValues memory t) = _getValues(tAmount);
            _tOwned[sender] = _tOwned[sender].sub(t.tAmount);
            _rOwned[sender] = _rOwned[sender].sub(r.rAmount);
            _tOwned[recipient] = _tOwned[recipient].add(t.tTransferAmount);
            _rOwned[recipient] = _rOwned[recipient].add(r.rTransferAmount);        
            _takeLiquidity(t.tLiquidity);
            _reflectFee(r.rFee, t.tFee);
            _takeRebateFee(t.tRebate);
            _toBurn(t.tBuyBurning);
            _toSafe(t.tSafe);
            _toBurn(t.tSellBurning);
            _toPool(t.tPool);
            _takeSellBonusFee(t.tSellBonus);
            emit Transfer(sender, recipient, t.tTransferAmount);
        }
    }

    function _transferToExcluded(address sender, address recipient, uint256 tAmount, bool takeFee) private {
        if (!takeFee) {
            uint256 rAmount = _getValue(tAmount);
            _rOwned[sender] = _rOwned[sender].sub(rAmount);
            _tOwned[recipient] = _tOwned[recipient].add(tAmount);
            _rOwned[recipient] = _rOwned[recipient].add(rAmount);  
            emit Transfer(sender, recipient, tAmount);
        } else {
            (RValues memory r, TValues memory t) = _getValues(tAmount);
            _rOwned[sender] = _rOwned[sender].sub(r.rAmount);
            _tOwned[recipient] = _tOwned[recipient].add(t.tTransferAmount);
            _rOwned[recipient] = _rOwned[recipient].add(r.rTransferAmount);         

            _takeLiquidity(t.tLiquidity);
            _reflectFee(r.rFee, t.tFee);
            _takeRebateFee(t.tRebate);
            _toBurn(t.tBuyBurning);
            _toSafe(t.tSafe);
            _toBurn(t.tSellBurning);
            _toPool(t.tPool);
            _takeSellBonusFee(t.tSellBonus);
            emit Transfer(sender, recipient, t.tTransferAmount);
        }
    }

    function _transferFromExcluded(address sender, address recipient, uint256 tAmount, bool takeFee) private {
        if (!takeFee) {
            uint256 rAmount = _getValue(tAmount);
            _tOwned[sender] = _tOwned[sender].sub(tAmount);
            _rOwned[sender] = _rOwned[sender].sub(rAmount);
            _rOwned[recipient] = _rOwned[recipient].add(rAmount);  
            emit Transfer(sender, recipient, tAmount);
        } else {
            (RValues memory r, TValues memory t) = _getValues(tAmount);
            _tOwned[sender] = _tOwned[sender].sub(t.tAmount);
            _rOwned[sender] = _rOwned[sender].sub(r.rAmount);
            _rOwned[recipient] = _rOwned[recipient].add(r.rTransferAmount);   

            _takeLiquidity(t.tLiquidity);
            _reflectFee(r.rFee, t.tFee);
            _takeRebateFee(t.tRebate);
            _toBurn(t.tBuyBurning);
            _toSafe(t.tSafe);
            _toBurn(t.tSellBurning);
            _toPool(t.tPool);
            _takeSellBonusFee(t.tSellBonus);
            emit Transfer(sender, recipient, t.tTransferAmount);
        }
    }

    function ownerWithdraw(address _token, address _to) public onlyOwner {
        if (_token == address(0x0)) {
            payable(_to).transfer(address(this).balance);
            return;
        }

        IERC20 token = IERC20(_token);
        token.transfer(_to, token.balanceOf(address(this)));
    }

}
