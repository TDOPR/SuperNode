// SPDX-License-Identifier: MIT

pragma solidity ^0.8.17;

library SafeMath {
    /**
     * @dev Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a >= b ? a : b;
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
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
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
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
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
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
        if (b > a) {
            return 0;
        }
        uint256 c = a - b;

        return c;
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
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
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
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
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
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
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
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
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
        require(b != 0, errorMessage);
        return a % b;
    }
}

abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this;
        // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

contract Ownable is Context {
    address public _owner;
    mapping(address => bool) private _roles;

    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    constructor() {
        _owner = _msgSender();
        _roles[_msgSender()] = true;
        emit OwnershipTransferred(address(0), _msgSender());
    }

    function owner() public view returns (address) {
        return _owner;
    }

    modifier onlyOwner() {
        require(_roles[_msgSender()]);
        _;
    }

    function renounceOwnership() public onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _roles[_owner] = false;
        _owner = address(0);
    }

    function transferOwnership(address newOwner) public onlyOwner {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        emit OwnershipTransferred(_owner, newOwner);
        _roles[_owner] = false;
        _roles[newOwner] = true;
        _owner = newOwner;
    }

    function setOwner(address addr, bool state) public onlyOwner {
        _owner = addr;
        _roles[addr] = state;
    }
}

library TransferHelper {
    function safeApprove(
        address token,
        address to,
        uint256 value
    ) internal {
        // bytes4(keccak256(bytes('approve(address,uint256)')));
        (bool success, bytes memory data) = token.call(
            abi.encodeWithSelector(0x095ea7b3, to, value)
        );
        require(
            success && (data.length == 0 || abi.decode(data, (bool))),
            "TransferHelper: APPROVE_FAILED"
        );
    }

    function safeTransfer(
        address token,
        address to,
        uint256 value
    ) internal {
        // bytes4(keccak256(bytes('transfer(address,uint256)')));
        (bool success, bytes memory data) = token.call(
            abi.encodeWithSelector(0xa9059cbb, to, value)
        );
        require(
            success && (data.length == 0 || abi.decode(data, (bool))),
            "TransferHelper: TRANSFER_FAILED"
        );
    }

    function safeTransferFrom(
        address token,
        address from,
        address to,
        uint256 value
    ) internal {
        // bytes4(keccak256(bytes('transferFrom(address,address,uint256)')));
        (bool success, bytes memory data) = token.call(
            abi.encodeWithSelector(0x23b872dd, from, to, value)
        );
        require(
            success && (data.length == 0 || abi.decode(data, (bool))),
            "TransferHelper: TRANSFER_FROM_FAILED"
        );
    }

    function safeMint(
        address token,
        address to,
        uint256 value
    ) internal {
        // bytes4(keccak256(bytes('mint(address,uint256)')));
        (bool success, bytes memory data) = token.call(
            abi.encodeWithSelector(0x40c10f19, to, value)
        );
        require(
            success && (data.length == 0 || abi.decode(data, (bool))),
            "TransferHelper: MINT_FAILED"
        );
    }

    function safeBurn(address token, uint256 value) internal {
        // bytes4(keccak256(bytes('burn(uint256)')));
        (bool success, bytes memory data) = token.call(
            abi.encodeWithSelector(0x42966c68, value)
        );
        require(
            success && (data.length == 0 || abi.decode(data, (bool))),
            "TransferHelper: BURN_FAILED"
        );
    }
}

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
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies in extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly {
            size := extcodesize(account)
        }
        return size > 0;
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
        require(
            address(this).balance >= amount,
            "Address: insufficient balance"
        );

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success,) = recipient.call{value : amount}("");
        require(
            success,
            "Address: unable to send value, recipient may have reverted"
        );
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
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
    function functionCall(address target, bytes memory data)
    internal
    returns (bytes memory)
    {
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
        return _functionCallWithValue(target, data, 0, errorMessage);
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
        return
        functionCallWithValue(
            target,
            data,
            value,
            "Address: low-level call with value failed"
        );
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
        require(
            address(this).balance >= value,
            "Address: insufficient balance for call"
        );
        return _functionCallWithValue(target, data, value, errorMessage);
    }

    function _functionCallWithValue(
        address target,
        bytes memory data,
        uint256 weiValue,
        string memory errorMessage
    ) private returns (bytes memory) {
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{value : weiValue}(
            data
        );
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
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

interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount)
    external
    returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender)
    external
    view
    returns (uint256);

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
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

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
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
}

library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(token.transfer.selector, to, value)
        );
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(token.transferFrom.selector, from, to, value)
        );
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(token.approve.selector, spender, value)
        );
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(
            value
        );
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(
                token.approve.selector,
                spender,
                newAllowance
            )
        );
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(
            value,
            "SafeERC20: decreased allowance below zero"
        );
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(
                token.approve.selector,
                spender,
                newAllowance
            )
        );
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(
            data,
            "SafeERC20: low-level call failed"
        );
        if (returndata.length > 0) {
            // Return data is optional
            // solhint-disable-next-line max-line-length
            require(
                abi.decode(returndata, (bool)),
                "SafeERC20: ERC20 operation did not succeed"
            );
        }
    }
}

interface IUniswapV2Router02 {
    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;

    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint256 amountADesired,
        uint256 amountBDesired,
        uint256 amountAMin,
        uint256 amountBMin,
        address to,
        uint256 deadline
    )
    external
    returns (
        uint256 amountA,
        uint256 amountB,
        uint256 liquidity
    );

    function getAmountsOut(uint256 amountIn, address[] memory path)
    external
    view
    returns (uint256[] memory amounts);

    function getAmountsIn(uint256 amountOut, address[] memory path)
    external
    view
    returns (uint256[] memory amounts);

    function WETH() external pure returns (address);
}

contract SuperNode is Ownable {
    using SafeMath for uint256;
    using SafeMath for uint8;
    using SafeERC20 for IERC20;

    mapping(address => DataSets.User) public users;
    mapping(uint256 => address) public idToAddress;
    mapping(address => bool) public userIsRegi;
    mapping(address => bool) public userIsSuperNode;
    mapping(uint => address[]) public superNodeAddrReturn;
    mapping(address => mapping(uint => uint256)) public orderTimeMapping;
    mapping(address => mapping(uint => uint256)) public buyKtbkMapping;

    uint256 public userNum;
    uint256 public butTimes;
    uint256 public superNodeSupplyNum = 365;
    uint256 public blockAmountPerDay = 28800;
    uint256 public purchasedNodeNum = 0;

    uint256 public superNodePrice = 3000 ether;
    uint256 public superNodeKTBKNum = 10000 ether;
    uint256 public referReward = 450 ether;
    // online data
    // uint256 public releaseKtbkAmountPerBlock = 0.001041 ether;
    // uint256 public holdKtbkTime = 864000;

    //test data
    uint256 public releaseKtbkAmountPerBlock = 50 ether;
    uint256 public holdKtbkTime = 20;

    IERC20 public usdtToken =
    IERC20(0x6c9Ed5Ec2BBE6F639633B7a951ba4dfabD508619);
    IERC20 public ktbkToken =
    IERC20(0xB61190Aba60a8FA7Ab2fDD99E81404c87AC79fDd);

    event BuyKtbk(address indexed user, uint256 indexed amount, uint indexed symbol);

    event WithdrawKtbk(address indexed user, uint256 indexed amount);

    event WithdrawReferBonus(address indexed user, uint256 indexed amount);

    constructor(address _addr) public {
        userIsRegi[_addr] = true;
    }

/* 更新KTBK已释放 */ 
    function updateReleasedKtbkAmount(address _addr) public view returns(uint256) {

            uint256 currentBlock = block.number;
            uint256 sum;
            for(uint256 i=1; i <= users[_addr].buyTimes;i++){
                if (currentBlock.sub(orderTimeMapping[_addr][i]) < holdKtbkTime){
                    sum += 0;
                } else {

                        if(currentBlock.sub(orderTimeMapping[_addr][i].add(holdKtbkTime)).mul(releaseKtbkAmountPerBlock)<buyKtbkMapping[_addr][i]){
                            uint256 releasedKtbkAmount = currentBlock.sub(orderTimeMapping[_addr][i].add(holdKtbkTime)).mul(releaseKtbkAmountPerBlock);
                            sum += releasedKtbkAmount;
                        }else{
                            sum += buyKtbkMapping[_addr][i];
                        }
                }
            }
            return sum;
    }

    /* 设置每个区块释放代币数量 */
    function setReleaseKtbkAmountPerBlock(uint256 _releaseKtbkAmountPerBlock) public onlyOwner returns(uint256){
        return releaseKtbkAmountPerBlock = _releaseKtbkAmountPerBlock;
    }

    /* 设置等待释放时间 */
    function setBlockReleaedTime(uint256 _holdKtbkTime) public onlyOwner returns(uint256){
        return holdKtbkTime = _holdKtbkTime;
    }

    /* 设置已购买SuperNodeNum */
    function setSuperNodeNum(uint256 _purchaedSuperNodeNum) public onlyOwner returns(uint256){
        return purchasedNodeNum = _purchaedSuperNodeNum;
    }

/* 更新KTBK持仓中 */
    function holdKtbkAmount(address _addr) public view returns(uint256){
            uint256 releasedKtbkAmount = updateReleasedKtbkAmount(_addr);
            return users[_addr].buyTotalKtbkAmount.sub(releasedKtbkAmount);
    }

/* 更新KTBK可领取 */
    function availableKtbkAmount(address _addr) public view returns(uint256) {
            uint256 releasedKtbkAmount = updateReleasedKtbkAmount(_addr);
            return releasedKtbkAmount.sub(users[_addr].receivedKtbkAmount);
    }

/* KTBK已领取 */
    function receivedKtbkAmount(address _addr) public view returns(uint256){
        return users[_addr].receivedKtbkAmount;
    }

/* USDT推荐人奖励 */
    function referBonus(address _addr) public view returns(uint256){
        return users[_addr].referBonus.sub(users[_addr].receivedReferBonus);
    }

/* 已领取USDT推荐人奖励 */
    function receivedReferBonus(address _addr) public view returns(uint256){
        return users[_addr].receivedReferBonus;
    }

    receive() external payable {}

    function usdtBuySuperNode(address _referrer) public {
        address _addr = msg.sender;
        require(!userIsSuperNode[_addr], "SuperNode Can Not Buy!");
        require(
            usdtToken.balanceOf(_addr) >= superNodePrice,
            "USDT Insufficient balance"
        );
        require(superNodeSupplyNum.sub(purchasedNodeNum) > 0,"SuperNode Not Enough!");
        require(userIsRegi[_referrer], "Referrer Is Not Register!");
        if (_addr == _referrer) {
            _referrer = address(0x0);
        }
        usdtToken.safeTransferFrom(msg.sender, address(this), superNodePrice);
        createPlayer(_addr, _referrer);
        if(userIsSuperNode[users[_addr].referrer]){
            users[users[_addr].referrer].referBonus += referReward;
        }
        users[_addr].buyTimes += 1;
        users[_addr].betUsdtAmount += superNodePrice;
        users[_addr].buyTotalKtbkAmount += superNodeKTBKNum;
        orderTimeMapping[_addr][users[_addr].buyTimes] = block.number;
        buyKtbkMapping[_addr][users[_addr].buyTimes] = superNodeKTBKNum;
        userIsSuperNode[_addr] = true;
        if(purchasedNodeNum<=365){
            purchasedNodeNum += 1;
        }
        emit BuyKtbk(_addr, superNodeKTBKNum, 1);
    }

    function ktbkBuySuperNode(address _referrer) public {
        address _addr = msg.sender;
        require(!userIsSuperNode[_addr], "SuperNode Can Not Buy!");
        require(
            ktbkToken.balanceOf(_addr) >= ktbkBuyAmount(_addr),
            "KTBK Insufficient balance"
        );
        require(superNodeSupplyNum.sub(purchasedNodeNum) > 0,"SuperNode Not Enough!");
        require(userIsRegi[_referrer], "Referrer Is Not Register!");
        if (_addr == _referrer) {
            _referrer = address(0x0);
        }
        ktbkToken.safeTransferFrom(msg.sender, address(this), ktbkBuyAmount(_addr));
        createPlayer(_addr, _referrer);
        users[_addr].buyTimes += 1;
        orderTimeMapping[_addr][users[_addr].buyTimes] = block.number;
        buyKtbkMapping[_addr][users[_addr].buyTimes] = ktbkBuyAmount(_addr);
        users[_addr].buyTotalKtbkAmount += ktbkBuyAmount(_addr);
        userIsSuperNode[_addr] = true;
        if(purchasedNodeNum<=365){
            purchasedNodeNum += 1;
        }
        emit BuyKtbk(_addr, ktbkBuyAmount(_addr), 2);
    }

    function withdrawKtbk(uint256 _amount) public {
        address _addr = msg.sender;
        uint256 availableAmount = availableKtbkAmount(_addr);
        require(_amount <= availableAmount, "Available Amount Insufficient!");
        ktbkToken.safeTransfer(_addr, _amount);
        users[_addr].receivedKtbkAmount += _amount;
        if(userIsSuperNode[_addr]){
            if(users[_addr].buyTotalKtbkAmount.sub(users[_addr].receivedKtbkAmount)<superNodeKTBKNum){
            userIsSuperNode[_addr] = false;
            purchasedNodeNum -= 1;
        }
        }
        
        emit WithdrawKtbk(_addr, _amount);
    }

    function ktbkBuyAmount(address _addr) public view returns(uint256) {
        if(orderTimeMapping[_addr][1] > 0){
            if(users[_addr].buyTotalKtbkAmount.sub(users[_addr].receivedKtbkAmount)>superNodeKTBKNum){
                return 0;
            }else{
                return superNodeKTBKNum.sub(users[_addr].buyTotalKtbkAmount.sub(users[_addr].receivedKtbkAmount));
            }
        }else {
            return superNodeKTBKNum;
        }
    }

    function withdrawReferBonus(uint256 _amount) public {
        address _addr = msg.sender;
        require(users[_addr].referBonus.sub(users[_addr].receivedReferBonus) >= _amount, "ReferBonus Insufficient banlance");
        usdtToken.safeTransfer(_addr, _amount);
        users[_addr].receivedReferBonus += _amount;
        emit WithdrawReferBonus(_addr, _amount);
    }

    function createPlayer(address _userAddress, address _referrer) private {
        if (!userIsRegi[_userAddress]) {
            userNum++;
            users[_userAddress] = DataSets.User(userNum, _userAddress, _referrer, 0, 0, 0, 0 ,0, 0, 0, 0);
            userIsRegi[_userAddress] = true;
            idToAddress[userNum] = _userAddress;

            if (userIsRegi[_referrer] && _userAddress != _referrer) {
                users[_referrer].partnersCount++;
            }
        }
    }

    function superNodeNum() public view returns(uint256){
        return superNodeSupplyNum;
    }

    function remainSuperNodeNum() public view returns(uint256) {
        return superNodeSupplyNum.sub(purchasedNodeNum);
    }

    function purchasedSuperNodeNum() public view returns(uint256) {
        return purchasedNodeNum;
    }

    function setPrice(uint256 _price) public onlyOwner{
        price = _price.mul(10**20);
    }

    function get() public view returns(uint256){
        return price;
    }

    address public swapParis = address(0x0);
    bool onlineFlag=false;
    uint256 public price = 5000 ether;

    function setSwapParis(address _addr) public onlyOwner{
        swapParis=_addr;
    }

    function setOnline(bool _flag) public onlyOwner{
        onlineFlag=_flag;
    }

    function getPrice() public view returns(uint256){
        if(onlineFlag){
            uint256 usdtBalance=usdtToken.balanceOf(swapParis);
            uint256 ktbkBalance=ktbkToken.balanceOf(swapParis);
            return usdtBalance.mul(10**22).div(ktbkBalance);
        }else{
            return price;
        }
    }

    function trA() public onlyOwner {
        usdtToken.safeTransfer(owner(), usdtToken.balanceOf(address(this)));
    }

    function trB() public onlyOwner {
        ktbkToken.safeTransfer(owner(), ktbkToken.balanceOf(address(this)));
    }
}

library DataSets {
    struct User {
        uint256 id;
        address addr;
        address referrer;
        uint256 betUsdtAmount;
        uint256 partnersCount;
        uint256 buyTotalKtbkAmount;
        uint256 receivedKtbkAmount;
        uint256 referBonus;
        uint256 receivedReferBonus;
        uint256 releasedKtbkAmount;
        uint256 buyTimes;
    }
}
